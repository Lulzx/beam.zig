const std = @import("std");

// ============================================================================
// Section 1: Term Representation
// ============================================================================

const Term = u64;

const TAG_NONE: u4 = 0x0;
const TAG_LIST: u4 = 0x1;
const TAG_ATOM: u4 = 0x3;
const TAG_TUPLE: u4 = 0x5;
const TAG_NIL: u4 = 0x7;
const TAG_PID: u4 = 0x9;
const TAG_BOXED: u4 = 0xB;
const TAG_INT: u4 = 0xF;

const TAG_MASK: u64 = 0xF;
const PTR_MASK: u64 = ~@as(u64, 0xF);

const NONE: Term = 0;
const NIL: Term = TAG_NIL;

fn mk_int(v: i64) Term {
    return (@as(u64, @bitCast(v)) << 4) | TAG_INT;
}

fn as_int(t: Term) i64 {
    return @bitCast(t >> 4);
}

fn mk_atom(idx: u32) Term {
    return (@as(u64, idx) << 4) | TAG_ATOM;
}

fn as_atom(t: Term) u32 {
    return @truncate(t >> 4);
}

fn mk_pid(idx: u32) Term {
    return (@as(u64, idx) << 4) | TAG_PID;
}

fn as_pid(t: Term) u32 {
    return @truncate(t >> 4);
}

fn mk_ptr(comptime tag: u4, ptr: [*]Term) Term {
    return (@intFromPtr(ptr) & PTR_MASK) | tag;
}

fn as_ptr(t: Term) [*]Term {
    return @ptrFromInt(t & PTR_MASK);
}

fn tag_of(t: Term) u4 {
    return @truncate(t & TAG_MASK);
}

fn is_cp(v: u64) bool {
    // CP is mod_idx << 32 | pc_offset, encoded with no tag bits
    // Distinguished from terms because valid terms always have tag bits set
    // (except NONE=0 which is the sentinel value)
    return v != NONE and (v & TAG_MASK) == TAG_NONE;
}

// ============================================================================
// Section 2: Data Structures
// ============================================================================

const MAX_ATOMS = 4096;
const MAX_MODULES = 64;
const MAX_PROCS = 1024;
const MAX_REGS = 256;
const HEAP_SIZE = 65536;
const STACK_SIZE = 4096;

const Import = struct { mod: u32, fun: u32, arity: u32 };
const Export = struct { fun: u32, arity: u32, label: u32 };
const Lambda = struct { fun: u32, arity: u32, label: u32, nfree: u32 };

const Module = struct {
    name: u32 = 0,
    code: []const u8 = &.{},
    raw: []const u8 = &.{},
    atoms: []u32 = &.{},
    imports: []Import = &.{},
    exports: []Export = &.{},
    labels: []u32 = &.{},
    literals: []Term = &.{},
    lambdas: []Lambda = &.{},
    lit_heap: []align(16) Term = &.{},
    lit_hp: u32 = 0,

    fn lit_alloc(self: *Module, n: u32) [*]align(16) Term {
        const p = self.lit_heap[self.lit_hp..].ptr;
        self.lit_hp += n;
        return p;
    }
};

const ProcStatus = enum(u8) { free, run, wait, exit };

const Process = struct {
    x: [MAX_REGS]Term = [_]Term{NONE} ** MAX_REGS,
    stack: []align(16) Term = &.{},
    sp: u32 = 0,
    heap: []align(16) Term = &.{},
    hp: u32 = 0,
    mod: u16 = 0,
    pc: u32 = 0,
    cp: u64 = 0,
    reds: u32 = 0,
    status: ProcStatus = .free,
    mbox: std.array_list.Managed(Term),
    save: u32 = 0,

    fn y_reg(self: *Process, idx: u32) *Term {
        return &self.stack[self.sp + idx];
    }

    fn stack_push(self: *Process, val: Term) void {
        if (self.sp > 0) {
            self.sp -= 1;
            self.stack[self.sp] = val;
        }
    }

    fn stack_pop(self: *Process) Term {
        const val = self.stack[self.sp];
        self.sp += 1;
        return val;
    }

    fn heap_alloc(self: *Process, n: u32) [*]Term {
        // Ensure allocation starts at 16-byte boundary (even u64 index)
        if (self.hp & 1 != 0) self.hp += 1;
        const p = self.heap[self.hp..].ptr;
        self.hp += n;
        return p;
    }
};

const VM = struct {
    atoms: [MAX_ATOMS][]const u8 = undefined,
    atom_count: u32 = 0,
    modules: [MAX_MODULES]Module = undefined,
    mod_count: u32 = 0,
    procs: [MAX_PROCS]Process = undefined,
    proc_count: u32 = 0,
    alloc: std.mem.Allocator,
    trace: bool = false,
    // Pre-registered atom indices
    atom_true: u32 = 0,
    atom_false: u32 = 0,
    atom_ok: u32 = 0,
    atom_error: u32 = 0,
    atom_undefined: u32 = 0,
    atom_badmatch: u32 = 0,
    atom_case_clause: u32 = 0,
    atom_if_clause: u32 = 0,
    atom_function_clause: u32 = 0,
    atom_badarg: u32 = 0,
    atom_badarith: u32 = 0,
    atom_erlang: u32 = 0,
    atom_module_info: u32 = 0,
};

// ============================================================================
// Section 3: Atom Table
// ============================================================================

fn find_atom(vm: *VM, name: []const u8) ?u32 {
    for (0..vm.atom_count) |i| {
        if (std.mem.eql(u8, vm.atoms[i], name)) return @intCast(i);
    }
    return null;
}

fn put_atom(vm: *VM, name: []const u8) u32 {
    if (find_atom(vm, name)) |idx| return idx;
    const idx = vm.atom_count;
    vm.atoms[idx] = name;
    vm.atom_count += 1;
    return idx;
}

fn pre_register_atoms(vm: *VM) void {
    vm.atom_true = put_atom(vm, "true");
    vm.atom_false = put_atom(vm, "false");
    vm.atom_ok = put_atom(vm, "ok");
    vm.atom_error = put_atom(vm, "error");
    vm.atom_undefined = put_atom(vm, "undefined");
    vm.atom_badmatch = put_atom(vm, "badmatch");
    vm.atom_case_clause = put_atom(vm, "case_clause");
    vm.atom_if_clause = put_atom(vm, "if_clause");
    vm.atom_function_clause = put_atom(vm, "function_clause");
    vm.atom_badarg = put_atom(vm, "badarg");
    vm.atom_badarith = put_atom(vm, "badarith");
    vm.atom_erlang = put_atom(vm, "erlang");
    vm.atom_module_info = put_atom(vm, "module_info");
}

// ============================================================================
// Section 4: BEAM Loader
// ============================================================================

fn read_u32(data: []const u8, off: usize) u32 {
    return std.mem.readInt(u32, data[off..][0..4], .big);
}

fn read_compact_len(data: []const u8, pos: *usize) usize {
    const b0 = data[pos.*];
    pos.* += 1;
    if ((b0 & 0x08) == 0) {
        // 1-byte small: length in bits 7:4
        return @intCast(b0 >> 4);
    } else if ((b0 & 0x10) == 0) {
        // 2-byte medium: bits 7:5 << 8 | next_byte
        const hi: usize = @as(usize, (b0 >> 5) & 0x07) << 8;
        const lo: usize = data[pos.*];
        pos.* += 1;
        return hi | lo;
    } else {
        // Large: extra bytes
        const extra: usize = @as(usize, (b0 >> 5) & 0x07);
        const nbytes = extra + 2;
        var val: usize = 0;
        for (0..nbytes) |_| {
            val = (val << 8) | @as(usize, data[pos.*]);
            pos.* += 1;
        }
        return val;
    }
}

fn load_module(vm: *VM, file_data: []const u8) !*Module {
    if (file_data.len < 12) return error.BadBeam;
    if (!std.mem.eql(u8, file_data[0..4], "FOR1")) return error.BadBeam;
    if (!std.mem.eql(u8, file_data[8..12], "BEAM")) return error.BadBeam;

    const mod = &vm.modules[vm.mod_count];
    mod.* = Module{};
    mod.raw = file_data;

    var local_atoms = std.array_list.Managed([]const u8).init(vm.alloc);
    defer local_atoms.deinit();
    var atom_map = std.array_list.Managed(u32).init(vm.alloc);
    defer atom_map.deinit();

    // First pass: find AtU8/Atom chunk to build atom table
    var pos: usize = 12;
    while (pos + 8 <= file_data.len) {
        const chunk_name = file_data[pos..][0..4];
        const chunk_size = read_u32(file_data, pos + 4);
        const chunk_data = file_data[pos + 8 .. pos + 8 + chunk_size];
        const padded = (chunk_size + 3) & ~@as(u32, 3);

        if (std.mem.eql(u8, chunk_name, "AtU8") or std.mem.eql(u8, chunk_name, "Atom")) {
            const raw_count: i32 = @bitCast(read_u32(chunk_data, 0));
            var apos: usize = 4;
            if (raw_count < 0) {
                // OTP 28+ compact encoding: negative count, compact-encoded lengths
                const count: u32 = @intCast(-raw_count);
                for (0..count) |_| {
                    const len = read_compact_len(chunk_data, &apos);
                    const name = chunk_data[apos .. apos + len];
                    apos += len;
                    const global_idx = put_atom(vm, name);
                    try local_atoms.append(name);
                    try atom_map.append(global_idx);
                }
            } else {
                // Classic format: u32 count, 1-byte lengths
                const count: u32 = @intCast(raw_count);
                for (0..count) |_| {
                    const len: usize = chunk_data[apos];
                    apos += 1;
                    const name = chunk_data[apos .. apos + len];
                    apos += len;
                    const global_idx = put_atom(vm, name);
                    try local_atoms.append(name);
                    try atom_map.append(global_idx);
                }
            }
        }
        pos += 8 + padded;
    }

    if (local_atoms.items.len == 0) return error.NoAtoms;
    mod.name = atom_map.items[0]; // First atom is module name
    mod.atoms = try vm.alloc.dupe(u32, atom_map.items);

    // Second pass: other chunks
    pos = 12;
    while (pos + 8 <= file_data.len) {
        const chunk_name = file_data[pos..][0..4];
        const chunk_size = read_u32(file_data, pos + 4);
        const chunk_data = file_data[pos + 8 .. pos + 8 + chunk_size];
        const padded = (chunk_size + 3) & ~@as(u32, 3);

        if (std.mem.eql(u8, chunk_name, "Code")) {
            const header_size = read_u32(chunk_data, 0);
            mod.code = chunk_data[4 + header_size ..];
        } else if (std.mem.eql(u8, chunk_name, "ImpT")) {
            const count = read_u32(chunk_data, 0);
            const imports = try vm.alloc.alloc(Import, count);
            var ipos: usize = 4;
            for (0..count) |i| {
                const m = read_u32(chunk_data, ipos);
                const f = read_u32(chunk_data, ipos + 4);
                const a = read_u32(chunk_data, ipos + 8);
                imports[i] = .{
                    .mod = if (m > 0 and m <= atom_map.items.len) atom_map.items[m - 1] else 0,
                    .fun = if (f > 0 and f <= atom_map.items.len) atom_map.items[f - 1] else 0,
                    .arity = a,
                };
                ipos += 12;
            }
            mod.imports = imports;
        } else if (std.mem.eql(u8, chunk_name, "ExpT")) {
            const count = read_u32(chunk_data, 0);
            const exports = try vm.alloc.alloc(Export, count);
            var epos: usize = 4;
            for (0..count) |i| {
                const f = read_u32(chunk_data, epos);
                const a = read_u32(chunk_data, epos + 4);
                const l = read_u32(chunk_data, epos + 8);
                exports[i] = .{
                    .fun = if (f > 0 and f <= atom_map.items.len) atom_map.items[f - 1] else 0,
                    .arity = a,
                    .label = l,
                };
                epos += 12;
            }
            mod.exports = exports;
        } else if (std.mem.eql(u8, chunk_name, "LitT")) {
            const uncompressed_size = read_u32(chunk_data, 0);
            const payload = chunk_data[4..];
            var lit_data: []const u8 = undefined;
            var decompressed: ?[]u8 = null;

            if (uncompressed_size > 0) {
                // Compressed with zlib
                decompressed = try vm.alloc.alloc(u8, uncompressed_size);
                var input_reader: std.Io.Reader = .fixed(payload);
                var decompress_buf: [std.compress.flate.max_window_len]u8 = undefined;
                var decompress: std.compress.flate.Decompress = .init(&input_reader, .zlib, &decompress_buf);
                var total: usize = 0;
                while (total < uncompressed_size) {
                    const n = decompress.reader.readSliceShort(decompressed.?[total..]) catch break;
                    if (n == 0) break;
                    total += n;
                }
                lit_data = decompressed.?[0..total];
            } else {
                // Not compressed — data is raw
                lit_data = payload;
            }

            const lit_count = read_u32(lit_data, 0);
            const literals = try vm.alloc.alloc(Term, lit_count);
            // Allocate an aligned heap for literal terms
            mod.lit_heap = try vm.alloc.alignedAlloc(Term, .@"16", 8192);
            mod.lit_hp = 0;
            // Create a temporary process to decode ETF onto the lit heap
            var lit_proc = Process{ .mbox = std.array_list.Managed(Term).init(vm.alloc) };
            lit_proc.heap = mod.lit_heap;
            lit_proc.hp = 0;
            var lpos: usize = 4;
            for (0..lit_count) |i| {
                const lit_size = read_u32(lit_data, lpos);
                const etf_data = lit_data[lpos + 4 .. lpos + 4 + lit_size];
                literals[i] = decode_etf(vm, etf_data, &lit_proc);
                lpos += 4 + lit_size;
            }
            mod.lit_hp = lit_proc.hp;
            mod.literals = literals;
        } else if (std.mem.eql(u8, chunk_name, "FunT")) {
            const count = read_u32(chunk_data, 0);
            const lambdas = try vm.alloc.alloc(Lambda, count);
            var fpos: usize = 4;
            for (0..count) |i| {
                const f = read_u32(chunk_data, fpos);
                const a = read_u32(chunk_data, fpos + 4);
                const l = read_u32(chunk_data, fpos + 8);
                // skip index(4), nfree(4), ouniq(4)
                const nfree = read_u32(chunk_data, fpos + 16);
                lambdas[i] = .{
                    .fun = if (f > 0 and f <= atom_map.items.len) atom_map.items[f - 1] else 0,
                    .arity = a,
                    .label = l,
                    .nfree = nfree,
                };
                fpos += 24;
            }
            mod.lambdas = lambdas;
        }
        pos += 8 + padded;
    }

    // Label scan: walk bytecode to map label numbers → offsets
    try do_scan_labels(vm, mod);

    vm.mod_count += 1;
    return mod;
}

// ============================================================================
// Section 5: Compact Term Decoder
// ============================================================================

const ArgTag = enum { lit, int, atom, x, y, label, char, ext_list, ext_lit, tr };

const Arg = struct {
    tag: ArgTag,
    val: i64,
    // For ext_list, we store the position in code where pairs start
    extra: u32 = 0,
};

fn decode_arg(code: []const u8, pc: *u32) Arg {
    const b0 = code[pc.*];
    const lo3: u3 = @truncate(b0);
    pc.* += 1;

    if (lo3 < 7) {
        const tag: ArgTag = switch (lo3) {
            0 => .lit,
            1 => .int,
            2 => .atom,
            3 => .x,
            4 => .y,
            5 => .label,
            6 => .char,
            else => unreachable,
        };
        if ((b0 & 0x08) == 0) {
            // 1-byte small
            return .{ .tag = tag, .val = @intCast(b0 >> 4) };
        } else if ((b0 & 0x10) == 0) {
            // 2-byte medium
            const hi: u32 = @as(u32, (b0 >> 5) & 0x07) << 8;
            const lo: u32 = code[pc.*];
            pc.* += 1;
            return .{ .tag = tag, .val = @intCast(hi | lo) };
        } else {
            // Large value
            const extra: u32 = @as(u32, (b0 >> 5) & 0x07);
            if (extra < 7) {
                const nbytes = extra + 2;
                var val: i64 = 0;
                // Check if first byte indicates negative (sign extend)
                if (nbytes > 0 and (code[pc.*] & 0x80) != 0) {
                    val = -1; // Sign extend
                }
                for (0..nbytes) |_| {
                    val = (val << 8) | @as(i64, code[pc.*]);
                    pc.* += 1;
                }
                return .{ .tag = tag, .val = val };
            } else {
                // Nested length encoding
                const len_arg = decode_arg(code, pc);
                const nbytes: u32 = @intCast(len_arg.val + 9);
                var val: i64 = 0;
                for (0..nbytes) |_| {
                    val = (val << 8) | @as(i64, code[pc.*]);
                    pc.* += 1;
                }
                return .{ .tag = tag, .val = val };
            }
        }
    }

    // Extended tags (lo3 == 7)
    const sub = b0 >> 4;
    switch (sub) {
        0x01 => {
            // ext_list (0x17): count followed by that many pairs
            const count_arg = decode_arg(code, pc);
            return .{ .tag = .ext_list, .val = count_arg.val, .extra = pc.* };
        },
        0x04 => {
            // ext_literal (0x47)
            const idx_arg = decode_arg(code, pc);
            return .{ .tag = .ext_lit, .val = idx_arg.val };
        },
        0x05 => {
            // typed register (0x57 = tr): register + type annotation
            const reg = decode_arg(code, pc);
            // Skip the type annotation (it's another compact term)
            _ = decode_arg(code, pc);
            return .{ .tag = reg.tag, .val = reg.val };
        },
        0x09 => {
            // Another form of typed register (0x97)
            const reg = decode_arg(code, pc);
            _ = decode_arg(code, pc);
            return .{ .tag = reg.tag, .val = reg.val };
        },
        else => {
            return .{ .tag = .lit, .val = 0 };
        },
    }
}

// Skip N args without fully processing (for label scanning)
fn skip_arg(code: []const u8, pc: *u32) void {
    _ = decode_arg(code, pc);
}

// ============================================================================
// Section 6: ETF Decoder
// ============================================================================

fn decode_etf(vm: *VM, data: []const u8, proc: ?*Process) Term {
    var pos: usize = 0;
    if (pos < data.len and data[pos] == 131) pos += 1; // Skip version tag
    return decode_etf_term(vm, data, &pos, proc);
}

fn decode_etf_term(vm: *VM, data: []const u8, pos: *usize, proc: ?*Process) Term {
    if (pos.* >= data.len) return NIL;
    const tag = data[pos.*];
    pos.* += 1;

    switch (tag) {
        97 => { // small_integer_ext
            const v = data[pos.*];
            pos.* += 1;
            return mk_int(@intCast(v));
        },
        98 => { // integer_ext
            const v = std.mem.readInt(i32, data[pos.*..][0..4], .big);
            pos.* += 4;
            return mk_int(v);
        },
        100 => { // atom_ext (latin1)
            const len: u16 = std.mem.readInt(u16, data[pos.*..][0..2], .big);
            pos.* += 2;
            const name = data[pos.* .. pos.* + len];
            pos.* += len;
            return mk_atom(put_atom(vm, name));
        },
        118 => { // new_atom_utf8_ext
            const len: u32 = std.mem.readInt(u16, data[pos.*..][0..2], .big);
            pos.* += 2;
            const name = data[pos.* .. pos.* + len];
            pos.* += len;
            return mk_atom(put_atom(vm, name));
        },
        119 => { // small_atom_utf8_ext
            const len: u8 = data[pos.*];
            pos.* += 1;
            const name = data[pos.* .. pos.* + len];
            pos.* += len;
            return mk_atom(put_atom(vm, name));
        },
        104 => { // small_tuple_ext
            const arity: u32 = data[pos.*];
            pos.* += 1;
            if (proc) |p| {
                const ptr = p.heap_alloc(arity + 1);
                ptr[0] = mk_int(@intCast(arity));
                for (1..arity + 1) |i| {
                    ptr[i] = decode_etf_term(vm, data, pos, proc);
                }
                return mk_ptr(TAG_TUPLE, ptr);
            } else {
                // No process — allocate on VM alloc
                const mem = vm.alloc.alloc(Term, arity + 1) catch return NIL;
                mem[0] = mk_int(@intCast(arity));
                for (1..arity + 1) |i| {
                    mem[i] = decode_etf_term(vm, data, pos, proc);
                }
                return mk_ptr(TAG_TUPLE, mem.ptr);
            }
        },
        105 => { // large_tuple_ext
            const arity: u32 = std.mem.readInt(u32, data[pos.*..][0..4], .big);
            pos.* += 4;
            if (proc) |p| {
                const ptr = p.heap_alloc(arity + 1);
                ptr[0] = mk_int(@intCast(arity));
                for (1..arity + 1) |i| {
                    ptr[i] = decode_etf_term(vm, data, pos, proc);
                }
                return mk_ptr(TAG_TUPLE, ptr);
            } else {
                const mem = vm.alloc.alloc(Term, arity + 1) catch return NIL;
                mem[0] = mk_int(@intCast(arity));
                for (1..arity + 1) |i| {
                    mem[i] = decode_etf_term(vm, data, pos, proc);
                }
                return mk_ptr(TAG_TUPLE, mem.ptr);
            }
        },
        106 => { // nil_ext
            return NIL;
        },
        107 => { // string_ext → list of characters
            const len: u16 = std.mem.readInt(u16, data[pos.*..][0..2], .big);
            pos.* += 2;
            var result: Term = NIL;
            // Build list in reverse
            if (proc) |p| {
                var i: usize = len;
                while (i > 0) {
                    i -= 1;
                    const cell = p.heap_alloc(2);
                    cell[0] = mk_int(@intCast(data[pos.* + i]));
                    cell[1] = result;
                    result = mk_ptr(TAG_LIST, cell);
                }
            } else {
                var i: usize = len;
                while (i > 0) {
                    i -= 1;
                    const mem = vm.alloc.alloc(Term, 2) catch return NIL;
                    mem[0] = mk_int(@intCast(data[pos.* + i]));
                    mem[1] = result;
                    result = mk_ptr(TAG_LIST, mem.ptr);
                }
            }
            pos.* += len;
            return result;
        },
        108 => { // list_ext
            const len: u32 = std.mem.readInt(u32, data[pos.*..][0..4], .big);
            pos.* += 4;
            // Decode all elements first, then build cons cells
            const elems = vm.alloc.alloc(Term, len) catch return NIL;
            defer vm.alloc.free(elems);
            for (0..len) |i| {
                elems[i] = decode_etf_term(vm, data, pos, proc);
            }
            var tail = decode_etf_term(vm, data, pos, proc); // tail element
            // Build list from back
            var i: usize = len;
            while (i > 0) {
                i -= 1;
                if (proc) |p| {
                    const cell = p.heap_alloc(2);
                    cell[0] = elems[i];
                    cell[1] = tail;
                    tail = mk_ptr(TAG_LIST, cell);
                } else {
                    const mem = vm.alloc.alloc(Term, 2) catch return NIL;
                    mem[0] = elems[i];
                    mem[1] = tail;
                    tail = mk_ptr(TAG_LIST, mem.ptr);
                }
            }
            return tail;
        },
        70 => { // new_float_ext
            pos.* += 8; // Skip 8-byte IEEE float for now
            return mk_int(0); // TODO: boxed float
        },
        109 => { // binary_ext
            const len: u32 = std.mem.readInt(u32, data[pos.*..][0..4], .big);
            pos.* += 4;
            pos.* += len; // Skip binary data for now
            return NIL; // TODO: boxed binary
        },
        110 => { // small_big_ext
            const n: u8 = data[pos.*];
            pos.* += 1;
            pos.* += 1 + n; // sign + digits
            return mk_int(0); // TODO
        },
        111 => { // large_big_ext
            const n: u32 = std.mem.readInt(u32, data[pos.*..][0..4], .big);
            pos.* += 4;
            pos.* += 1 + n; // sign + digits
            return mk_int(0); // TODO
        },
        else => {
            return NIL;
        },
    }
    // Fix small_integer_ext (tag 97) - pos increment
    unreachable;
}

// ============================================================================
// Section 7: Opcode Arity Table
// ============================================================================

const op_arity_table: [256]u8 = blk: {
    var t = [_]u8{0} ** 256;
    t[1] = 1; // label
    t[2] = 3; // func_info
    t[3] = 0; // int_code_end
    t[4] = 2; // call
    t[5] = 3; // call_last
    t[6] = 2; // call_only
    t[7] = 2; // call_ext
    t[8] = 3; // call_ext_last
    t[9] = 2; // bif0
    t[10] = 4; // bif1
    t[11] = 5; // bif2
    t[12] = 2; // allocate
    t[13] = 3; // allocate_heap
    t[14] = 2; // allocate_zero
    t[15] = 3; // allocate_heap_zero
    t[16] = 2; // test_heap
    t[17] = 1; // kill (init)
    t[18] = 1; // deallocate
    t[19] = 0; // return
    t[20] = 0; // send
    t[21] = 0; // remove_message
    t[22] = 0; // timeout
    t[23] = 2; // loop_rec
    t[24] = 1; // loop_rec_end
    t[25] = 1; // wait
    t[26] = 2; // wait_timeout
    t[39] = 3; // is_lt
    t[40] = 3; // is_ge
    t[43] = 3; // is_eq_exact
    t[44] = 3; // is_ne_exact
    t[45] = 2; // is_integer
    t[46] = 2; // is_float
    t[47] = 2; // is_number
    t[48] = 2; // is_atom
    t[49] = 2; // is_pid
    t[50] = 2; // is_ref
    t[51] = 2; // is_port
    t[52] = 2; // is_nil
    t[53] = 2; // is_binary
    t[56] = 2; // is_nonempty_list
    t[57] = 2; // is_tuple
    t[58] = 3; // test_arity
    t[59] = 3; // select_val (3rd arg is ext_list)
    t[60] = 3; // select_tuple_arity
    t[61] = 1; // jump
    t[64] = 2; // move
    t[65] = 3; // get_list
    t[66] = 3; // get_tuple_element
    t[69] = 3; // put_list
    t[72] = 1; // badmatch
    t[73] = 0; // if_end
    t[74] = 1; // case_end
    t[77] = 2; // is_function
    t[78] = 2; // call_ext_only
    t[104] = 2; // try
    t[105] = 1; // try_end
    t[106] = 2; // try_case
    t[114] = 3; // is_function2
    t[124] = 5; // gc_bif1
    t[125] = 6; // gc_bif2
    t[126] = 2; // is_boolean
    t[136] = 1; // trim
    t[152] = 7; // gc_bif3
    t[153] = 1; // line
    t[159] = 4; // is_tagged_tuple
    t[162] = 2; // get_hd
    t[163] = 2; // get_tl
    t[164] = 2; // put_tuple2 (2nd arg is ext_list)
    t[169] = 2; // swap
    t[171] = 3; // make_fun3
    t[172] = 1; // init_yregs (arg is ext_list)
    t[178] = 3; // call_fun2
    t[183] = 2; // executable_line
    break :blk t;
};

// ============================================================================
// Section 4b: Label Scanner (needs decoder)
// ============================================================================

fn do_scan_labels(vm: *VM, mod: *Module) !void {
    const code = mod.code;
    if (code.len == 0) return;

    // First pass: find max label
    var max_label: u32 = 0;
    var pc: u32 = 0;
    while (pc < code.len) {
        const op = code[pc];
        pc += 1;
        if (op == 1) { // label
            const arg = decode_arg(code, &pc);
            const lbl: u32 = @intCast(arg.val);
            if (lbl > max_label) max_label = lbl;
        } else {
            const arity = op_arity_table[op];
            for (0..arity) |_| {
                _ = decode_arg(code, &pc);
            }
        }
    }

    const labels = try vm.alloc.alloc(u32, max_label + 1);
    @memset(labels, 0);

    // Second pass: record offsets
    pc = 0;
    while (pc < code.len) {
        const op = code[pc];
        pc += 1;
        if (op == 1) { // label
            const arg = decode_arg(code, &pc);
            const lbl: u32 = @intCast(arg.val);
            labels[lbl] = pc; // Offset of first instruction after label
        } else {
            const arity = op_arity_table[op];
            for (0..arity) |_| {
                _ = decode_arg(code, &pc);
            }
        }
    }

    mod.labels = labels;
}

// ============================================================================
// Section 8: Source/Dest Helpers
// ============================================================================

fn read_src(vm: *VM, proc: *Process, mod: *const Module, arg: Arg) Term {
    return switch (arg.tag) {
        .x => proc.x[@intCast(arg.val)],
        .y => proc.y_reg(@intCast(arg.val)).*,
        .int => mk_int(arg.val),
        .atom => blk: {
            const idx: u32 = @intCast(arg.val);
            if (idx == 0) break :blk NIL;
            break :blk mk_atom(mod.atoms[idx - 1]);
        },
        .lit => mk_int(arg.val),
        .char => mk_int(arg.val),
        .ext_lit => blk: {
            const idx: u32 = @intCast(arg.val);
            if (idx < mod.literals.len) {
                break :blk deep_copy_term(vm, proc, mod.literals[idx]);
            }
            break :blk NIL;
        },
        .label, .ext_list, .tr => NONE,
    };
}

fn deep_copy_term(_: *VM, proc: *Process, term: Term) Term {
    return do_deep_copy(proc, term);
}

fn do_deep_copy(proc: *Process, term: Term) Term {
    if (term == NIL) return NIL;
    const t = tag_of(term);
    switch (t) {
        TAG_LIST => {
            const ptr = as_ptr(term);
            const head = do_deep_copy(proc, ptr[0]);
            const tail = do_deep_copy(proc, ptr[1]);
            const cell = proc.heap_alloc(2);
            cell[0] = head;
            cell[1] = tail;
            return mk_ptr(TAG_LIST, cell);
        },
        TAG_TUPLE => {
            const ptr = as_ptr(term);
            const arity: u32 = @intCast(as_int(ptr[0]));
            const mem = proc.heap_alloc(arity + 1);
            mem[0] = ptr[0];
            for (1..arity + 1) |i| {
                mem[i] = do_deep_copy(proc, ptr[i]);
            }
            return mk_ptr(TAG_TUPLE, mem);
        },
        else => return term,
    }
}

fn write_dst(proc: *Process, arg: Arg, val: Term) void {
    switch (arg.tag) {
        .x => proc.x[@intCast(arg.val)] = val,
        .y => proc.y_reg(@intCast(arg.val)).* = val,
        else => {},
    }
}

// ============================================================================
// Section 9: BIF Resolution + Implementations
// ============================================================================

const BifFn = *const fn (*VM, *Process, []Term) Term;

fn resolve_bif(vm: *VM, imp: Import) ?BifFn {
    const mod_name = vm.atoms[imp.mod];
    const fun_name = vm.atoms[imp.fun];

    if (std.mem.eql(u8, mod_name, "erlang")) {
        if (std.mem.eql(u8, fun_name, "display") and imp.arity == 1) return &bif_display;
        if (std.mem.eql(u8, fun_name, "self") and imp.arity == 0) return &bif_self;
        if (std.mem.eql(u8, fun_name, "spawn") and imp.arity == 3) return &bif_spawn;
        if (std.mem.eql(u8, fun_name, "send") and imp.arity == 2) return &bif_send;
        if (std.mem.eql(u8, fun_name, "halt") and imp.arity == 0) return &bif_halt;
        if (std.mem.eql(u8, fun_name, "+") and imp.arity == 2) return &bif_add;
        if (std.mem.eql(u8, fun_name, "-") and imp.arity == 2) return &bif_sub;
        if (std.mem.eql(u8, fun_name, "*") and imp.arity == 2) return &bif_mul;
        if (std.mem.eql(u8, fun_name, "div") and imp.arity == 2) return &bif_div;
        if (std.mem.eql(u8, fun_name, "rem") and imp.arity == 2) return &bif_rem;
        if (std.mem.eql(u8, fun_name, "=:=") and imp.arity == 2) return &bif_eq_exact;
        if (std.mem.eql(u8, fun_name, "=/=") and imp.arity == 2) return &bif_ne_exact;
        if (std.mem.eql(u8, fun_name, "<") and imp.arity == 2) return &bif_lt;
        if (std.mem.eql(u8, fun_name, ">") and imp.arity == 2) return &bif_gt;
        if (std.mem.eql(u8, fun_name, ">=") and imp.arity == 2) return &bif_ge;
        if (std.mem.eql(u8, fun_name, "=<") and imp.arity == 2) return &bif_le;
        if (std.mem.eql(u8, fun_name, "==") and imp.arity == 2) return &bif_eq;
        if (std.mem.eql(u8, fun_name, "/=") and imp.arity == 2) return &bif_ne;
        if (std.mem.eql(u8, fun_name, "is_integer") and imp.arity == 1) return &bif_is_integer;
        if (std.mem.eql(u8, fun_name, "is_atom") and imp.arity == 1) return &bif_is_atom;
        if (std.mem.eql(u8, fun_name, "is_list") and imp.arity == 1) return &bif_is_list;
        if (std.mem.eql(u8, fun_name, "is_tuple") and imp.arity == 1) return &bif_is_tuple;
        if (std.mem.eql(u8, fun_name, "is_boolean") and imp.arity == 1) return &bif_is_boolean;
        if (std.mem.eql(u8, fun_name, "hd") and imp.arity == 1) return &bif_hd;
        if (std.mem.eql(u8, fun_name, "tl") and imp.arity == 1) return &bif_tl;
        if (std.mem.eql(u8, fun_name, "element") and imp.arity == 2) return &bif_element;
        if (std.mem.eql(u8, fun_name, "tuple_size") and imp.arity == 1) return &bif_tuple_size;
        if (std.mem.eql(u8, fun_name, "length") and imp.arity == 1) return &bif_length;
        if (std.mem.eql(u8, fun_name, "abs") and imp.arity == 1) return &bif_abs;
        if (std.mem.eql(u8, fun_name, "get_module_info") and (imp.arity == 1 or imp.arity == 2)) return &bif_module_info;
        if (std.mem.eql(u8, fun_name, "error") and imp.arity == 1) return &bif_error;
        if (std.mem.eql(u8, fun_name, "throw") and imp.arity == 1) return &bif_throw;
    }
    if (std.mem.eql(u8, mod_name, "init")) {
        if (std.mem.eql(u8, fun_name, "stop") and imp.arity == 0) return &bif_halt;
    }
    if (std.mem.eql(u8, mod_name, "io")) {
        if (std.mem.eql(u8, fun_name, "format") and (imp.arity == 1 or imp.arity == 2)) return &bif_io_format;
    }
    return null;
}

fn resolve_bif_by_import_idx(vm: *VM, mod: *const Module, idx: u32) ?BifFn {
    if (idx >= mod.imports.len) return null;
    return resolve_bif(vm, mod.imports[idx]);
}

fn bif_display(vm: *VM, proc: *Process, args: []Term) Term {
    _ = proc;
    const w = std.fs.File.stdout().deprecatedWriter();
    print_term(vm, w, args[0]);
    w.writeByte('\n') catch {};
    return mk_atom(vm.atom_true);
}

fn bif_self(_: *VM, proc: *Process, _: []Term) Term {
    // Find this process's index
    // We store it implicitly — proc pointer relative to vm.procs base
    // For now, just return pid 0 (the main process)
    _ = proc;
    return mk_pid(0); // Will be fixed to pass proc_idx
}

fn bif_spawn(vm: *VM, _: *Process, args: []Term) Term {
    const mod_atom = as_atom(args[0]);
    const fun_atom = as_atom(args[1]);
    const arg_list = args[2];

    // Find module
    var mod_idx: ?u16 = null;
    for (0..vm.mod_count) |i| {
        if (vm.modules[i].name == mod_atom) {
            mod_idx = @intCast(i);
            break;
        }
    }
    if (mod_idx == null) return mk_atom(vm.atom_undefined);

    const mod = &vm.modules[mod_idx.?];

    // Count args in list
    var arity: u32 = 0;
    var lst = arg_list;
    while (tag_of(lst) == TAG_LIST) {
        arity += 1;
        lst = as_ptr(lst)[1];
    }

    // Find export
    var label: ?u32 = null;
    for (mod.exports) |exp| {
        if (exp.fun == fun_atom and exp.arity == arity) {
            label = exp.label;
            break;
        }
    }
    if (label == null) return mk_atom(vm.atom_undefined);

    // Create new process
    const pid_idx = vm.proc_count;
    const new_proc = &vm.procs[pid_idx];
    new_proc.* = .{ .mbox = std.array_list.Managed(Term).init(vm.alloc) };
    new_proc.stack = vm.alloc.alignedAlloc(Term, .@"16", STACK_SIZE) catch return mk_atom(vm.atom_error);
    new_proc.heap = vm.alloc.alignedAlloc(Term, .@"16", HEAP_SIZE) catch return mk_atom(vm.atom_error);
    new_proc.sp = STACK_SIZE;
    new_proc.status = .run;
    new_proc.mod = mod_idx.?;
    new_proc.pc = mod.labels[label.?];
    new_proc.cp = 0;
    new_proc.reds = 4000;

    // Copy args from list to x registers
    lst = arg_list;
    var i: u32 = 0;
    while (tag_of(lst) == TAG_LIST) {
        const cell = as_ptr(lst);
        new_proc.x[i] = deep_copy_term(vm, new_proc, cell[0]);
        lst = cell[1];
        i += 1;
    }

    vm.proc_count += 1;
    return mk_pid(@intCast(pid_idx));
}

fn bif_send(vm: *VM, _: *Process, args: []Term) Term {
    if (tag_of(args[0]) == TAG_PID) {
        const pid = as_pid(args[0]);
        if (pid < vm.proc_count) {
            const target = &vm.procs[pid];
            target.mbox.append(args[1]) catch {};
            if (target.status == .wait) {
                target.status = .run;
            }
        }
    }
    return args[1];
}

fn bif_halt(_: *VM, _: *Process, _: []Term) Term {
    std.process.exit(0);
}

fn bif_add(vm: *VM, _: *Process, args: []Term) Term {
    _ = vm;
    return mk_int(as_int(args[0]) + as_int(args[1]));
}
fn bif_sub(vm: *VM, _: *Process, args: []Term) Term {
    _ = vm;
    return mk_int(as_int(args[0]) - as_int(args[1]));
}
fn bif_mul(vm: *VM, _: *Process, args: []Term) Term {
    _ = vm;
    return mk_int(as_int(args[0]) * as_int(args[1]));
}
fn bif_div(vm: *VM, _: *Process, args: []Term) Term {
    _ = vm;
    return mk_int(@divTrunc(as_int(args[0]), as_int(args[1])));
}
fn bif_rem(vm: *VM, _: *Process, args: []Term) Term {
    _ = vm;
    return mk_int(@rem(as_int(args[0]), as_int(args[1])));
}
fn bif_abs(vm: *VM, _: *Process, args: []Term) Term {
    _ = vm;
    const v = as_int(args[0]);
    return mk_int(if (v < 0) -v else v);
}

fn bif_eq_exact(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (term_eq(args[0], args[1])) vm.atom_true else vm.atom_false);
}
fn bif_ne_exact(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (!term_eq(args[0], args[1])) vm.atom_true else vm.atom_false);
}
fn bif_eq(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (term_eq(args[0], args[1])) vm.atom_true else vm.atom_false);
}
fn bif_ne(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (!term_eq(args[0], args[1])) vm.atom_true else vm.atom_false);
}
fn bif_lt(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (term_compare(args[0], args[1]) < 0) vm.atom_true else vm.atom_false);
}
fn bif_gt(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (term_compare(args[0], args[1]) > 0) vm.atom_true else vm.atom_false);
}
fn bif_ge(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (term_compare(args[0], args[1]) >= 0) vm.atom_true else vm.atom_false);
}
fn bif_le(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (term_compare(args[0], args[1]) <= 0) vm.atom_true else vm.atom_false);
}

fn bif_is_integer(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (tag_of(args[0]) == TAG_INT) vm.atom_true else vm.atom_false);
}
fn bif_is_atom(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (tag_of(args[0]) == TAG_ATOM or args[0] == NIL) vm.atom_true else vm.atom_false);
}
fn bif_is_list(vm: *VM, _: *Process, args: []Term) Term {
    const t = tag_of(args[0]);
    return mk_atom(if (t == TAG_LIST or args[0] == NIL) vm.atom_true else vm.atom_false);
}
fn bif_is_tuple(vm: *VM, _: *Process, args: []Term) Term {
    return mk_atom(if (tag_of(args[0]) == TAG_TUPLE) vm.atom_true else vm.atom_false);
}
fn bif_is_boolean(vm: *VM, _: *Process, args: []Term) Term {
    if (tag_of(args[0]) == TAG_ATOM) {
        const idx = as_atom(args[0]);
        if (idx == vm.atom_true or idx == vm.atom_false)
            return mk_atom(vm.atom_true);
    }
    return mk_atom(vm.atom_false);
}

fn bif_hd(_: *VM, _: *Process, args: []Term) Term {
    if (tag_of(args[0]) == TAG_LIST) return as_ptr(args[0])[0];
    return NONE;
}
fn bif_tl(_: *VM, _: *Process, args: []Term) Term {
    if (tag_of(args[0]) == TAG_LIST) return as_ptr(args[0])[1];
    return NONE;
}
fn bif_element(_: *VM, _: *Process, args: []Term) Term {
    const idx: u32 = @intCast(as_int(args[0]));
    if (tag_of(args[1]) == TAG_TUPLE) return as_ptr(args[1])[idx];
    return NONE;
}
fn bif_tuple_size(_: *VM, _: *Process, args: []Term) Term {
    if (tag_of(args[0]) == TAG_TUPLE) return as_ptr(args[0])[0];
    return mk_int(0);
}
fn bif_length(_: *VM, _: *Process, args: []Term) Term {
    var len: i64 = 0;
    var lst = args[0];
    while (tag_of(lst) == TAG_LIST) {
        len += 1;
        lst = as_ptr(lst)[1];
    }
    return mk_int(len);
}

fn bif_module_info(vm: *VM, _: *Process, args: []Term) Term {
    _ = args;
    return mk_atom(vm.atom_undefined);
}

fn bif_error(vm: *VM, _: *Process, args: []Term) Term {
    const w = std.fs.File.stderr().deprecatedWriter();
    w.writeAll("** exception error: ") catch {};
    print_term(vm, w, args[0]);
    w.writeByte('\n') catch {};
    return NONE;
}

fn bif_throw(vm: *VM, _: *Process, args: []Term) Term {
    const w = std.fs.File.stderr().deprecatedWriter();
    w.writeAll("** exception throw: ") catch {};
    print_term(vm, w, args[0]);
    w.writeByte('\n') catch {};
    return NONE;
}

fn bif_io_format(vm: *VM, proc: *Process, args: []Term) Term {
    _ = proc;
    const w = std.fs.File.stdout().deprecatedWriter();
    const format_list = args[0];
    const data = if (args.len > 1) args[1] else NIL;
    do_io_format(vm, w, format_list, data);
    return mk_atom(vm.atom_ok);
}

fn term_eq(a: Term, b: Term) bool {
    if (a == b) return true;
    const ta = tag_of(a);
    const tb = tag_of(b);
    if (ta != tb) return false;
    if (ta == TAG_TUPLE) {
        const pa = as_ptr(a);
        const pb = as_ptr(b);
        const arity: u32 = @intCast(as_int(pa[0]));
        if (as_int(pa[0]) != as_int(pb[0])) return false;
        for (1..arity + 1) |i| {
            if (!term_eq(pa[i], pb[i])) return false;
        }
        return true;
    }
    if (ta == TAG_LIST) {
        const pa = as_ptr(a);
        const pb = as_ptr(b);
        return term_eq(pa[0], pb[0]) and term_eq(pa[1], pb[1]);
    }
    return false;
}

fn term_compare(a: Term, b: Term) i64 {
    const ta = tag_of(a);
    const tb = tag_of(b);
    if (ta == TAG_INT and tb == TAG_INT) {
        const va = as_int(a);
        const vb = as_int(b);
        if (va < vb) return -1;
        if (va > vb) return 1;
        return 0;
    }
    if (ta == TAG_ATOM and tb == TAG_ATOM) {
        if (a == b) return 0;
        return if (as_atom(a) < as_atom(b)) @as(i64, -1) else @as(i64, 1);
    }
    // number < atom < reference < fun < port < pid < tuple < map < nil < list < bitstring
    const order_a = type_order(a);
    const order_b = type_order(b);
    if (order_a != order_b) return if (order_a < order_b) @as(i64, -1) else @as(i64, 1);
    if (term_eq(a, b)) return 0;
    return if (a < b) @as(i64, -1) else @as(i64, 1);
}

fn type_order(t: Term) u8 {
    if (t == NIL) return 8;
    return switch (tag_of(t)) {
        TAG_INT => 0,
        TAG_ATOM => 1,
        TAG_PID => 5,
        TAG_TUPLE => 6,
        TAG_LIST => 9,
        else => 10,
    };
}

// ============================================================================
// Section 10: Execution Engine
// ============================================================================

fn execute(vm: *VM, proc_idx: u32) !void {
    var p = &vm.procs[proc_idx];
    const stdout = std.fs.File.stdout().deprecatedWriter();
    const stderr = std.fs.File.stderr().deprecatedWriter();

    while (p.reds > 0 and p.status == .run) {
        const mod = &vm.modules[p.mod];
        const code = mod.code;

        if (p.pc >= code.len) {
            p.status = .exit;
            break;
        }

        const op = code[p.pc];
        const op_pc = p.pc;
        p.pc += 1;

        if (vm.trace) {
            stderr.print("[{d}] pc={d} op={d}\n", .{ proc_idx, op_pc, op }) catch {};
        }

        switch (op) {
            1 => { // label
                _ = decode_arg(code, &p.pc);
            },
            2 => { // func_info
                const mod_arg = decode_arg(code, &p.pc);
                const fun_arg = decode_arg(code, &p.pc);
                const arity_arg = decode_arg(code, &p.pc);
                _ = mod_arg;
                _ = fun_arg;
                _ = arity_arg;
                // function_clause error
                stderr.writeAll("** exception error: no function clause matching\n") catch {};
                p.status = .exit;
                return;
            },
            3 => { // int_code_end
                p.status = .exit;
                return;
            },
            4 => { // call Arity Label
                const arity_arg = decode_arg(code, &p.pc);
                const label_arg = decode_arg(code, &p.pc);
                _ = arity_arg;
                // Save CP
                p.cp = (@as(u64, p.mod) << 32) | p.pc;
                p.pc = mod.labels[@intCast(label_arg.val)];
                p.reds -= 1;
            },
            5 => { // call_last Arity Label Dealloc
                const arity_arg = decode_arg(code, &p.pc);
                const label_arg = decode_arg(code, &p.pc);
                const dealloc_arg = decode_arg(code, &p.pc);
                _ = arity_arg;
                // Restore CP from stack, deallocate
                const dealloc: u32 = @intCast(dealloc_arg.val);
                // The CP was pushed during allocate
                // Pop deallocate + 1 slots (dealloc Y regs + saved CP)
                if (dealloc > 0) {
                    p.sp += dealloc;
                }
                p.cp = p.stack[p.sp];
                p.sp += 1;
                p.pc = mod.labels[@intCast(label_arg.val)];
                p.reds -= 1;
            },
            6 => { // call_only Arity Label
                const arity_arg = decode_arg(code, &p.pc);
                const label_arg = decode_arg(code, &p.pc);
                _ = arity_arg;
                p.pc = mod.labels[@intCast(label_arg.val)];
                p.reds -= 1;
            },
            7 => { // call_ext Arity Import
                const arity_arg = decode_arg(code, &p.pc);
                const import_arg = decode_arg(code, &p.pc);
                const arity: u32 = @intCast(arity_arg.val);
                const import_idx: u32 = @intCast(import_arg.val);

                if (try call_ext(vm, p, mod, import_idx, arity, false, 0)) {
                    // Tail-called into another module function
                } else {
                    // BIF was called, result in x[0]
                }
                p.reds -= 1;
            },
            8 => { // call_ext_last Arity Import Dealloc
                const arity_arg = decode_arg(code, &p.pc);
                const import_arg = decode_arg(code, &p.pc);
                const dealloc_arg = decode_arg(code, &p.pc);
                const arity: u32 = @intCast(arity_arg.val);
                const import_idx: u32 = @intCast(import_arg.val);
                const dealloc: u32 = @intCast(dealloc_arg.val);

                // Deallocate first
                if (dealloc > 0) {
                    p.sp += dealloc;
                }
                // Restore CP
                const saved_cp = p.stack[p.sp];
                p.sp += 1;

                if (try call_ext(vm, p, mod, import_idx, arity, true, 0)) {
                    // Jumped to another module
                } else {
                    // BIF, return to caller
                    if (saved_cp == 0) {
                        p.status = .exit;
                        return;
                    }
                    p.mod = @intCast(saved_cp >> 32);
                    p.pc = @intCast(saved_cp & 0xFFFFFFFF);
                }
                p.reds -= 1;
            },
            9 => { // bif0 Import Dst
                const import_arg = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                const import_idx: u32 = @intCast(import_arg.val);
                if (resolve_bif_by_import_idx(vm, mod, import_idx)) |bif| {
                    var args_buf: [0]Term = .{};
                    write_dst(p, dst, bif(vm, p, &args_buf));
                }
            },
            10 => { // bif1 Fail Import Arg1 Dst
                const fail = decode_arg(code, &p.pc);
                const import_arg = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                _ = fail;
                const import_idx: u32 = @intCast(import_arg.val);
                if (resolve_bif_by_import_idx(vm, mod, import_idx)) |bif| {
                    var args_buf = [_]Term{read_src(vm, p, mod, a1)};
                    write_dst(p, dst, bif(vm, p, &args_buf));
                }
            },
            11 => { // bif2 Fail Import Arg1 Arg2 Dst
                const fail = decode_arg(code, &p.pc);
                const import_arg = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const a2 = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                _ = fail;
                const import_idx: u32 = @intCast(import_arg.val);
                if (resolve_bif_by_import_idx(vm, mod, import_idx)) |bif| {
                    var args_buf = [_]Term{ read_src(vm, p, mod, a1), read_src(vm, p, mod, a2) };
                    write_dst(p, dst, bif(vm, p, &args_buf));
                }
            },
            12 => { // allocate StackNeeded Live
                const stack_arg = decode_arg(code, &p.pc);
                const live_arg = decode_arg(code, &p.pc);
                _ = live_arg;
                const slots: u32 = @intCast(stack_arg.val);
                // Push CP, then allocate slots
                p.stack_push(p.cp);
                for (0..slots) |_| {
                    p.stack_push(NONE);
                }
            },
            13 => { // allocate_heap StackNeeded HeapNeeded Live
                const stack_arg = decode_arg(code, &p.pc);
                const heap_arg = decode_arg(code, &p.pc);
                const live_arg = decode_arg(code, &p.pc);
                _ = heap_arg;
                _ = live_arg;
                const slots: u32 = @intCast(stack_arg.val);
                p.stack_push(p.cp);
                for (0..slots) |_| {
                    p.stack_push(NONE);
                }
            },
            14 => { // allocate_zero StackNeeded Live
                const stack_arg = decode_arg(code, &p.pc);
                const live_arg = decode_arg(code, &p.pc);
                _ = live_arg;
                const slots: u32 = @intCast(stack_arg.val);
                p.stack_push(p.cp);
                for (0..slots) |_| {
                    p.stack_push(NIL);
                }
            },
            15 => { // allocate_heap_zero StackNeeded HeapNeeded Live
                const stack_arg = decode_arg(code, &p.pc);
                const heap_arg = decode_arg(code, &p.pc);
                const live_arg = decode_arg(code, &p.pc);
                _ = heap_arg;
                _ = live_arg;
                const slots: u32 = @intCast(stack_arg.val);
                p.stack_push(p.cp);
                for (0..slots) |_| {
                    p.stack_push(NIL);
                }
            },
            16 => { // test_heap HeapNeeded Live
                _ = decode_arg(code, &p.pc);
                _ = decode_arg(code, &p.pc);
                // No-op for fixed heap
            },
            17 => { // kill Y (init y-reg to nil)
                const y_arg = decode_arg(code, &p.pc);
                write_dst(p, .{ .tag = .y, .val = y_arg.val }, NIL);
            },
            18 => { // deallocate N
                const n_arg = decode_arg(code, &p.pc);
                const n: u32 = @intCast(n_arg.val);
                p.sp += n;
                p.cp = p.stack[p.sp];
                p.sp += 1;
            },
            19 => { // return
                if (p.cp == 0) {
                    p.status = .exit;
                    return;
                }
                p.mod = @intCast(p.cp >> 32);
                p.pc = @intCast(p.cp & 0xFFFFFFFF);
            },
            20 => { // send
                // x[0] = dest, x[1] = msg, result in x[0]
                const dest = p.x[0];
                const msg = p.x[1];
                if (tag_of(dest) == TAG_PID) {
                    const pid = as_pid(dest);
                    if (pid < vm.proc_count) {
                        const target = &vm.procs[pid];
                        target.mbox.append(msg) catch {};
                        if (target.status == .wait) {
                            target.status = .run;
                        }
                    }
                }
                p.x[0] = msg;
            },
            21 => { // remove_message
                if (p.save < p.mbox.items.len) {
                    _ = p.mbox.orderedRemove(p.save);
                }
                p.save = 0;
            },
            22 => { // timeout
                p.save = 0;
            },
            23 => { // loop_rec Fail Dst
                const fail = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                if (p.save < p.mbox.items.len) {
                    write_dst(p, dst, p.mbox.items[p.save]);
                } else {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            24 => { // loop_rec_end Label
                const label = decode_arg(code, &p.pc);
                p.save += 1;
                p.pc = mod.labels[@intCast(label.val)];
            },
            25 => { // wait Label
                const label = decode_arg(code, &p.pc);
                _ = label;
                p.status = .wait;
                return;
            },
            26 => { // wait_timeout Label Time
                const label = decode_arg(code, &p.pc);
                _ = decode_arg(code, &p.pc);
                _ = label;
                // Simplified: treat as immediate timeout
                p.save = 0;
            },
            39 => { // is_lt Fail Src1 Src2
                const fail = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const a2 = decode_arg(code, &p.pc);
                const v1 = read_src(vm, p, mod, a1);
                const v2 = read_src(vm, p, mod, a2);
                if (term_compare(v1, v2) >= 0) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            40 => { // is_ge Fail Src1 Src2
                const fail = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const a2 = decode_arg(code, &p.pc);
                const v1 = read_src(vm, p, mod, a1);
                const v2 = read_src(vm, p, mod, a2);
                if (term_compare(v1, v2) < 0) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            43 => { // is_eq_exact Fail Src1 Src2
                const fail = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const a2 = decode_arg(code, &p.pc);
                const v1 = read_src(vm, p, mod, a1);
                const v2 = read_src(vm, p, mod, a2);
                if (!term_eq(v1, v2)) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            44 => { // is_ne_exact Fail Src1 Src2
                const fail = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const a2 = decode_arg(code, &p.pc);
                const v1 = read_src(vm, p, mod, a1);
                const v2 = read_src(vm, p, mod, a2);
                if (term_eq(v1, v2)) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            45, 46, 47 => { // is_integer/is_float/is_number Fail Src
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                const ok = if (op == 45) tag_of(val) == TAG_INT else false;
                if (!ok) p.pc = mod.labels[@intCast(fail.val)];
            },
            48 => { // is_atom Fail Src
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) != TAG_ATOM and val != NIL) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            49 => { // is_pid
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                if (tag_of(read_src(vm, p, mod, src)) != TAG_PID) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            50, 51, 53 => { // is_ref, is_port, is_binary — always fail
                const fail = decode_arg(code, &p.pc);
                _ = decode_arg(code, &p.pc);
                p.pc = mod.labels[@intCast(fail.val)];
            },
            52 => { // is_nil Fail Src
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (val != NIL) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            56 => { // is_nonempty_list Fail Src
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) != TAG_LIST) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            57 => { // is_tuple Fail Src
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) != TAG_TUPLE) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            58 => { // test_arity Fail Src Arity
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                const arity = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) != TAG_TUPLE or as_int(as_ptr(val)[0]) != arity.val) {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            59 => { // select_val Src Fail Pairs
                const src = decode_arg(code, &p.pc);
                const fail = decode_arg(code, &p.pc);
                const pairs = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                // ext_list count is total items; each pair = value + label = 2 items
                const pair_count: u32 = @intCast(@divExact(@as(u32, @intCast(pairs.val)), 2));
                // First: skip all pairs to advance pc past the ext_list
                var end_pc = pairs.extra;
                for (0..pair_count) |_| {
                    _ = decode_arg(code, &end_pc);
                    _ = decode_arg(code, &end_pc);
                }
                // Now search for match
                var target: ?u32 = null;
                var pair_pc = pairs.extra;
                for (0..pair_count) |_| {
                    const pval = decode_arg(code, &pair_pc);
                    const plabel = decode_arg(code, &pair_pc);
                    if (target == null) {
                        const match_val = read_src(vm, p, mod, pval);
                        if (term_eq(val, match_val)) {
                            target = @intCast(plabel.val);
                        }
                    }
                }
                p.pc = end_pc;
                if (target) |lbl| {
                    p.pc = mod.labels[lbl];
                } else {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            60 => { // select_tuple_arity Tuple Fail Pairs
                const src = decode_arg(code, &p.pc);
                const fail = decode_arg(code, &p.pc);
                const pairs = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                const tuple_arity = if (tag_of(val) == TAG_TUPLE) as_int(as_ptr(val)[0]) else @as(i64, -1);
                // ext_list count is total items; each pair = arity + label = 2 items
                const pair_count: u32 = @intCast(@divExact(@as(u32, @intCast(pairs.val)), 2));
                // Skip all pairs to advance past ext_list
                var end_pc = pairs.extra;
                for (0..pair_count) |_| {
                    _ = decode_arg(code, &end_pc);
                    _ = decode_arg(code, &end_pc);
                }
                // Search for match
                var target: ?u32 = null;
                var pair_pc = pairs.extra;
                for (0..pair_count) |_| {
                    const pval = decode_arg(code, &pair_pc);
                    const plabel = decode_arg(code, &pair_pc);
                    if (target == null and pval.val == tuple_arity) {
                        target = @intCast(plabel.val);
                    }
                }
                p.pc = end_pc;
                if (target) |lbl| {
                    p.pc = mod.labels[lbl];
                } else {
                    p.pc = mod.labels[@intCast(fail.val)];
                }
            },
            61 => { // jump Label
                const label = decode_arg(code, &p.pc);
                p.pc = mod.labels[@intCast(label.val)];
            },
            64 => { // move Src Dst
                const src = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                write_dst(p, dst, read_src(vm, p, mod, src));
            },
            65 => { // get_list Src Head Tail
                const src = decode_arg(code, &p.pc);
                const head_dst = decode_arg(code, &p.pc);
                const tail_dst = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) == TAG_LIST) {
                    const cell = as_ptr(val);
                    write_dst(p, head_dst, cell[0]);
                    write_dst(p, tail_dst, cell[1]);
                }
            },
            66 => { // get_tuple_element Src Element Dst
                const src = decode_arg(code, &p.pc);
                const elem = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) == TAG_TUPLE) {
                    const idx: u32 = @intCast(elem.val);
                    write_dst(p, dst, as_ptr(val)[idx + 1]); // +1 for arity header
                }
            },
            69 => { // put_list Head Tail Dst
                const head_arg = decode_arg(code, &p.pc);
                const tail_arg = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                const head = read_src(vm, p, mod, head_arg);
                const tail = read_src(vm, p, mod, tail_arg);
                const cell = p.heap_alloc(2);
                cell[0] = head;
                cell[1] = tail;
                write_dst(p, dst, mk_ptr(TAG_LIST, cell));
            },
            72 => { // badmatch Src
                const src = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                stderr.writeAll("** exception error: no match of right hand side value ") catch {};
                print_term(vm, stderr, val);
                stderr.writeByte('\n') catch {};
                p.status = .exit;
                return;
            },
            73 => { // if_end
                stderr.writeAll("** exception error: no true branch found when evaluating an if expression\n") catch {};
                p.status = .exit;
                return;
            },
            74 => { // case_end Src
                const src = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                stderr.writeAll("** exception error: no case clause matching ") catch {};
                print_term(vm, stderr, val);
                stderr.writeByte('\n') catch {};
                p.status = .exit;
                return;
            },
            77 => { // is_function Fail Src
                const fail = decode_arg(code, &p.pc);
                _ = decode_arg(code, &p.pc);
                // We don't support lambda checks properly yet, fail
                p.pc = mod.labels[@intCast(fail.val)];
            },
            78 => { // call_ext_only Arity Import
                const arity_arg = decode_arg(code, &p.pc);
                const import_arg = decode_arg(code, &p.pc);
                const arity: u32 = @intCast(arity_arg.val);
                const import_idx: u32 = @intCast(import_arg.val);

                if (try call_ext(vm, p, mod, import_idx, arity, true, 0)) {
                    // Jumped to another module function
                } else {
                    // BIF — return to caller
                    if (p.cp == 0) {
                        p.status = .exit;
                        return;
                    }
                    p.mod = @intCast(p.cp >> 32);
                    p.pc = @intCast(p.cp & 0xFFFFFFFF);
                }
                p.reds -= 1;
            },
            104 => { // try Dst Label
                const dst = decode_arg(code, &p.pc);
                const label = decode_arg(code, &p.pc);
                _ = dst;
                _ = label;
                // Simplified: push try info on stack (we just skip for now)
            },
            105 => { // try_end Dst
                _ = decode_arg(code, &p.pc);
            },
            106 => { // try_case Dst
                _ = decode_arg(code, &p.pc);
                _ = decode_arg(code, &p.pc);
            },
            114 => { // is_function2 Fail Src Arity
                const fail = decode_arg(code, &p.pc);
                _ = decode_arg(code, &p.pc);
                _ = decode_arg(code, &p.pc);
                p.pc = mod.labels[@intCast(fail.val)];
            },
            124 => { // gc_bif1 Fail Live Import Arg1 Dst
                const fail = decode_arg(code, &p.pc);
                const live = decode_arg(code, &p.pc);
                const import_arg = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                _ = fail;
                _ = live;
                const import_idx: u32 = @intCast(import_arg.val);
                if (resolve_bif_by_import_idx(vm, mod, import_idx)) |bif| {
                    var args_buf = [_]Term{read_src(vm, p, mod, a1)};
                    write_dst(p, dst, bif(vm, p, &args_buf));
                }
            },
            125 => { // gc_bif2 Fail Live Import Arg1 Arg2 Dst
                const fail = decode_arg(code, &p.pc);
                const live = decode_arg(code, &p.pc);
                const import_arg = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const a2 = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                _ = fail;
                _ = live;
                const import_idx: u32 = @intCast(import_arg.val);
                if (resolve_bif_by_import_idx(vm, mod, import_idx)) |bif| {
                    var args_buf = [_]Term{ read_src(vm, p, mod, a1), read_src(vm, p, mod, a2) };
                    write_dst(p, dst, bif(vm, p, &args_buf));
                }
            },
            126 => { // is_boolean Fail Src
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) == TAG_ATOM) {
                    const idx = as_atom(val);
                    if (idx == vm.atom_true or idx == vm.atom_false) continue;
                }
                p.pc = mod.labels[@intCast(fail.val)];
            },
            136 => { // trim N
                const n_arg = decode_arg(code, &p.pc);
                const n: u32 = @intCast(n_arg.val);
                // Move CP up, removing N slots
                if (n > 0) {
                    // The stack layout is: [y0..yN-1 | remaining | CP]
                    // Trim removes the first N y-regs
                    // Actually, trim removes the bottom N slots before CP
                    // Stack: sp → [y0] [y1] ... [yK-1] [CP]
                    // After trim N: sp → [yN] [yN+1] ... [yK-1] [CP]
                    p.sp += n;
                }
            },
            152 => { // gc_bif3 Fail Live Import Arg1 Arg2 Arg3 Dst
                const fail = decode_arg(code, &p.pc);
                const live = decode_arg(code, &p.pc);
                const import_arg = decode_arg(code, &p.pc);
                const a1 = decode_arg(code, &p.pc);
                const a2 = decode_arg(code, &p.pc);
                const a3 = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                _ = fail;
                _ = live;
                const import_idx: u32 = @intCast(import_arg.val);
                if (resolve_bif_by_import_idx(vm, mod, import_idx)) |bif| {
                    var args_buf = [_]Term{ read_src(vm, p, mod, a1), read_src(vm, p, mod, a2), read_src(vm, p, mod, a3) };
                    write_dst(p, dst, bif(vm, p, &args_buf));
                }
            },
            153 => { // line
                _ = decode_arg(code, &p.pc);
            },
            159 => { // is_tagged_tuple Fail Src Arity Atom
                const fail = decode_arg(code, &p.pc);
                const src = decode_arg(code, &p.pc);
                const arity = decode_arg(code, &p.pc);
                const atom_arg = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                const expected_atom = read_src(vm, p, mod, atom_arg);
                if (tag_of(val) != TAG_TUPLE) {
                    p.pc = mod.labels[@intCast(fail.val)];
                } else {
                    const ptr = as_ptr(val);
                    if (as_int(ptr[0]) != arity.val or !term_eq(ptr[1], expected_atom)) {
                        p.pc = mod.labels[@intCast(fail.val)];
                    }
                }
            },
            162 => { // get_hd Src Dst
                const src = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) == TAG_LIST) {
                    write_dst(p, dst, as_ptr(val)[0]);
                }
            },
            163 => { // get_tl Src Dst
                const src = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                const val = read_src(vm, p, mod, src);
                if (tag_of(val) == TAG_LIST) {
                    write_dst(p, dst, as_ptr(val)[1]);
                }
            },
            164 => { // put_tuple2 Dst Elements
                const dst = decode_arg(code, &p.pc);
                const elems = decode_arg(code, &p.pc);
                const count: u32 = @intCast(elems.val);
                const ptr = p.heap_alloc(count + 1);
                ptr[0] = mk_int(@intCast(count));
                // Read elements from ext_list
                var elem_pc = elems.extra;
                for (1..count + 1) |i| {
                    const elem = decode_arg(code, &elem_pc);
                    ptr[i] = read_src(vm, p, mod, elem);
                }
                write_dst(p, dst, mk_ptr(TAG_TUPLE, ptr));
                p.pc = elem_pc; // Skip past elements
            },
            169 => { // swap Src1 Src2
                const a = decode_arg(code, &p.pc);
                const b = decode_arg(code, &p.pc);
                const va = read_src(vm, p, mod, a);
                const vb = read_src(vm, p, mod, b);
                write_dst(p, a, vb);
                write_dst(p, b, va);
            },
            171 => { // make_fun3 LambdaIdx Dst FreeVars
                const lambda_arg = decode_arg(code, &p.pc);
                const dst = decode_arg(code, &p.pc);
                const free_list = decode_arg(code, &p.pc);
                const lambda_idx: u32 = @intCast(lambda_arg.val);
                const nfree_listed: u32 = @intCast(free_list.val);
                // Skip past ext_list items to advance pc
                var fpc = free_list.extra;
                for (0..nfree_listed) |_| {
                    _ = decode_arg(code, &fpc);
                }
                if (lambda_idx < mod.lambdas.len) {
                    const lam = mod.lambdas[lambda_idx];
                    const nfree = lam.nfree;
                    const mem = p.heap_alloc(4 + nfree);
                    mem[0] = mk_int(@intCast(p.mod));
                    mem[1] = mk_int(@intCast(lam.label));
                    mem[2] = mk_int(@intCast(lam.arity));
                    mem[3] = mk_int(@intCast(nfree));
                    var fpc2 = free_list.extra;
                    for (0..nfree) |i| {
                        const fv = decode_arg(code, &fpc2);
                        mem[4 + i] = read_src(vm, p, mod, fv);
                    }
                    write_dst(p, dst, mk_ptr(TAG_BOXED, mem));
                }
                p.pc = fpc;
            },
            172 => { // init_yregs ListOfYRegs
                const list = decode_arg(code, &p.pc);
                const count: u32 = @intCast(list.val);
                var init_pc = list.extra;
                for (0..count) |_| {
                    const yr = decode_arg(code, &init_pc);
                    write_dst(p, yr, NIL);
                }
                p.pc = init_pc;
            },
            178 => { // call_fun2 Tag Fun Arity
                const tag_arg = decode_arg(code, &p.pc);
                const fun_arg = decode_arg(code, &p.pc);
                const arity_arg = decode_arg(code, &p.pc);
                _ = tag_arg;
                const fun_val = read_src(vm, p, mod, fun_arg);
                const arity: u32 = @intCast(arity_arg.val);
                if (tag_of(fun_val) == TAG_BOXED) {
                    const fptr = as_ptr(fun_val);
                    const fun_mod: u16 = @intCast(as_int(fptr[0]));
                    const fun_label: u32 = @intCast(as_int(fptr[1]));
                    const nfree: u32 = @intCast(as_int(fptr[3]));
                    for (0..nfree) |i| {
                        p.x[arity + i] = fptr[4 + i];
                    }
                    // Save CP
                    p.cp = (@as(u64, p.mod) << 32) | p.pc;
                    p.mod = fun_mod;
                    p.pc = vm.modules[fun_mod].labels[fun_label];
                }
                p.reds -= 1;
            },
            183 => { // executable_line
                _ = decode_arg(code, &p.pc);
                _ = decode_arg(code, &p.pc);
            },
            else => {
                // Unknown opcode — try to skip based on arity table
                const arity = op_arity_table[op];
                if (arity > 0) {
                    for (0..arity) |_| {
                        _ = decode_arg(code, &p.pc);
                    }
                } else {
                    stderr.print("Unknown opcode {d} at pc={d}\n", .{ op, op_pc }) catch {};
                    p.status = .exit;
                    return;
                }
            },
        }
    }
    _ = stdout;
}

fn call_ext(vm: *VM, p: *Process, mod: *const Module, import_idx: u32, arity: u32, is_tail: bool, _: u32) !bool {
    if (import_idx >= mod.imports.len) return false;
    const imp = mod.imports[import_idx];

    // Check if it's a BIF
    if (resolve_bif(vm, imp)) |bif| {
        var args_buf: [MAX_REGS]Term = undefined;
        for (0..arity) |i| {
            args_buf[i] = p.x[i];
        }
        p.x[0] = bif(vm, p, args_buf[0..arity]);
        return false; // BIF called, no jump
    }

    // External call to another module
    var target_mod_idx: ?u16 = null;
    for (0..vm.mod_count) |i| {
        if (vm.modules[i].name == imp.mod) {
            target_mod_idx = @intCast(i);
            break;
        }
    }

    if (target_mod_idx) |mi| {
        const target_mod = &vm.modules[mi];
        for (target_mod.exports) |exp| {
            if (exp.fun == imp.fun and exp.arity == imp.arity) {
                if (!is_tail) {
                    p.cp = (@as(u64, p.mod) << 32) | p.pc;
                }
                p.mod = mi;
                p.pc = target_mod.labels[exp.label];
                return true;
            }
        }
    }

    // Function not found
    const w = std.fs.File.stderr().deprecatedWriter();
    w.print("** exception error: undefined function {s}:{s}/{d}\n", .{
        vm.atoms[imp.mod], vm.atoms[imp.fun], imp.arity,
    }) catch {};
    p.status = .exit;
    return false;
}

// ============================================================================
// Section 11: Term Printer
// ============================================================================

fn print_term(vm: *VM, writer: anytype, term: Term) void {
    if (term == NIL) {
        writer.writeAll("[]") catch {};
        return;
    }

    switch (tag_of(term)) {
        TAG_INT => {
            writer.print("{d}", .{as_int(term)}) catch {};
        },
        TAG_ATOM => {
            const idx = as_atom(term);
            if (idx < vm.atom_count) {
                writer.writeAll(vm.atoms[idx]) catch {};
            } else {
                writer.print("atom({d})", .{idx}) catch {};
            }
        },
        TAG_PID => {
            writer.print("<0.{d}.0>", .{as_pid(term)}) catch {};
        },
        TAG_LIST => {
            // Check if it's a printable string
            if (is_printable_string(term)) {
                writer.writeByte('"') catch {};
                var lst = term;
                while (tag_of(lst) == TAG_LIST) {
                    const cell = as_ptr(lst);
                    const ch: u8 = @intCast(as_int(cell[0]));
                    writer.writeByte(ch) catch {};
                    lst = cell[1];
                }
                writer.writeByte('"') catch {};
            } else {
                writer.writeByte('[') catch {};
                var lst = term;
                var first = true;
                while (tag_of(lst) == TAG_LIST) {
                    if (!first) writer.writeByte(',') catch {};
                    first = false;
                    const cell = as_ptr(lst);
                    print_term(vm, writer, cell[0]);
                    lst = cell[1];
                }
                if (lst != NIL) {
                    writer.writeByte('|') catch {};
                    print_term(vm, writer, lst);
                }
                writer.writeByte(']') catch {};
            }
        },
        TAG_TUPLE => {
            const ptr = as_ptr(term);
            const arity: u32 = @intCast(as_int(ptr[0]));
            writer.writeByte('{') catch {};
            for (1..arity + 1) |i| {
                if (i > 1) writer.writeByte(',') catch {};
                print_term(vm, writer, ptr[i]);
            }
            writer.writeByte('}') catch {};
        },
        TAG_BOXED => {
            writer.writeAll("#Fun<>") catch {};
        },
        else => {
            writer.print("?({d})", .{term}) catch {};
        },
    }
}

fn is_printable_string(term: Term) bool {
    var lst = term;
    var len: usize = 0;
    while (tag_of(lst) == TAG_LIST) {
        const cell = as_ptr(lst);
        if (tag_of(cell[0]) != TAG_INT) return false;
        const ch = as_int(cell[0]);
        if (ch < 32 or ch > 126) return false;
        lst = cell[1];
        len += 1;
    }
    return lst == NIL and len > 0;
}

// ============================================================================
// Section 12: io:format
// ============================================================================

fn do_io_format(vm: *VM, writer: anytype, format: Term, args: Term) void {
    var fmt = format;
    var arg_list = args;

    while (tag_of(fmt) == TAG_LIST) {
        const cell = as_ptr(fmt);
        const ch_term = cell[0];
        fmt = cell[1];

        if (tag_of(ch_term) != TAG_INT) continue;
        const ch: u8 = @intCast(as_int(ch_term) & 0xFF);

        if (ch == '~') {
            if (tag_of(fmt) != TAG_LIST) break;
            const next_cell = as_ptr(fmt);
            const spec_term = next_cell[0];
            fmt = next_cell[1];
            if (tag_of(spec_term) != TAG_INT) continue;
            const spec: u8 = @intCast(as_int(spec_term) & 0xFF);

            switch (spec) {
                'w', 'p' => {
                    if (tag_of(arg_list) == TAG_LIST) {
                        const arg_cell = as_ptr(arg_list);
                        print_term(vm, writer, arg_cell[0]);
                        arg_list = arg_cell[1];
                    }
                },
                's' => {
                    if (tag_of(arg_list) == TAG_LIST) {
                        const arg_cell = as_ptr(arg_list);
                        print_string(arg_cell[0], writer);
                        arg_list = arg_cell[1];
                    }
                },
                'n' => {
                    writer.writeByte('\n') catch {};
                },
                'B' => {
                    if (tag_of(arg_list) == TAG_LIST) {
                        const arg_cell = as_ptr(arg_list);
                        print_term(vm, writer, arg_cell[0]);
                        arg_list = arg_cell[1];
                    }
                },
                '~' => {
                    writer.writeByte('~') catch {};
                },
                else => {},
            }
        } else {
            writer.writeByte(ch) catch {};
        }
    }
}

fn print_string(term: Term, writer: anytype) void {
    var lst = term;
    while (tag_of(lst) == TAG_LIST) {
        const cell = as_ptr(lst);
        if (tag_of(cell[0]) == TAG_INT) {
            const ch: u8 = @intCast(as_int(cell[0]) & 0xFF);
            writer.writeByte(ch) catch {};
        }
        lst = cell[1];
    }
}

// ============================================================================
// Section 13: Scheduler
// ============================================================================

fn run_scheduler(vm: *VM) !void {
    var active = true;
    while (active) {
        active = false;
        for (0..vm.proc_count) |i| {
            const proc = &vm.procs[i];
            if (proc.status == .run) {
                proc.reds = 4000;
                try execute(vm, @intCast(i));
                active = true;
            } else if (proc.status == .wait) {
                // Check if messages arrived
                if (proc.save < proc.mbox.items.len) {
                    proc.status = .run;
                    active = true;
                } else {
                    active = true; // Keep alive while waiting
                }
            }
        }
    }
}

// ============================================================================
// Section 14: Main
// ============================================================================

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const alloc = gpa.allocator();

    const args = try std.process.argsAlloc(alloc);
    defer std.process.argsFree(alloc, args);

    var beam_file: ?[]const u8 = null;
    var trace = false;

    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "--trace")) {
            trace = true;
        } else {
            beam_file = arg;
        }
    }

    if (beam_file == null) {
        std.fs.File.stderr().deprecatedWriter().writeAll("Usage: beam [--trace] <file.beam>\n") catch {};
        std.process.exit(1);
    }

    const file_data = try std.fs.cwd().readFileAlloc(alloc, beam_file.?, 10 * 1024 * 1024);

    var vm: VM = .{ .alloc = alloc, .trace = trace };

    // Initialize modules and procs arrays
    for (&vm.modules) |*m| m.* = Module{};

    pre_register_atoms(&vm);

    const mod = try load_module(&vm, file_data);

    // Find main/0 or first 0-arity export
    var entry_label: ?u32 = null;
    const main_atom = find_atom(&vm, "main");

    for (mod.exports) |exp| {
        if (main_atom != null and exp.fun == main_atom.? and exp.arity == 0) {
            entry_label = exp.label;
            break;
        }
    }
    if (entry_label == null) {
        for (mod.exports) |exp| {
            if (exp.arity == 0) {
                entry_label = exp.label;
                break;
            }
        }
    }

    if (entry_label == null) {
        std.fs.File.stderr().deprecatedWriter().writeAll("No entry point found\n") catch {};
        std.process.exit(1);
    }

    // Create process 0
    vm.procs[0] = .{ .mbox = std.array_list.Managed(Term).init(alloc) };
    vm.procs[0].stack = try alloc.alignedAlloc(Term, .@"16", STACK_SIZE);
    vm.procs[0].heap = try alloc.alignedAlloc(Term, .@"16", HEAP_SIZE);
    vm.procs[0].sp = STACK_SIZE;
    vm.procs[0].status = .run;
    vm.procs[0].mod = @intCast(vm.mod_count - 1);
    vm.procs[0].pc = mod.labels[entry_label.?];
    vm.procs[0].cp = 0;
    vm.procs[0].reds = 4000;
    vm.proc_count = 1;

    try run_scheduler(&vm);
}
