# beam.zig

A minimalist BEAM virtual machine written in Zig. Single-file implementation (~3600 lines) that loads and executes `.beam` files compiled by `erlc`.

## Features

- Tagged u64 term representation (integers, atoms, lists, tuples, pids, boxed values)
- Boxed floats (IEEE 754), binaries, closures, and maps
- BEAM file loader with IFF chunk parsing (AtU8, Code, ImpT, ExpT, LitT, FunT)
- Compact term encoding decoder
- External Term Format (ETF) literal decoder (including floats, binaries, maps)
- Switch-dispatch execution engine (~60 opcodes including map operations)
- Round-robin process scheduler with message passing
- Pattern matching (select_val, select_tuple_arity, is_tagged_tuple, get_map_elements)
- Process dictionary (erlang:put/2, erlang:get/1)
- Named process registry (erlang:register/2, erlang:whereis/1)
- 50+ BIFs: arithmetic, comparison, type checks, list ops, conversions, maps, io:format

## Requirements

- Zig 0.15.2+
- Erlang/OTP (for compiling `.erl` test files with `erlc`)

## Build & Run

```sh
zig build
./zig-out/bin/beam test/hello.beam
```

With execution trace:

```sh
./zig-out/bin/beam --trace test/fib.beam
```

## Tests

```sh
# Compile test programs (requires erlc)
cd test && erlc *.erl && cd ..

# Run all tests
./zig-out/bin/beam test/hello.beam       # hello, 42, {ok,[1,2,3]}
./zig-out/bin/beam test/fac.beam         # 3628800
./zig-out/bin/beam test/fib.beam         # 6765
./zig-out/bin/beam test/list_ops.beam    # 15, [5,4,3,2,1]
./zig-out/bin/beam test/spawn_test.beam  # done, {hello,world}
./zig-out/bin/beam test/float_test.beam  # 3.14, 6.28, ...
./zig-out/bin/beam test/binary_test.beam # <<"hello">>, 5, ...
./zig-out/bin/beam test/map_test.beam    # #{a => 1,b => 2,c => 3}, ...
./zig-out/bin/beam test/convert_test.beam # "hello", world, "12345", ...
```

## Supported BIFs

**Arithmetic**: `+`, `-`, `*`, `/`, `div`, `rem`, `abs`, `max`, `min`, `band`, `bor`, `bxor`, `bnot`, `bsl`, `bsr`

**Comparison**: `=:=`, `=/=`, `==`, `/=`, `<`, `>`, `>=`, `=<`

**Type checks**: `is_integer`, `is_float`, `is_number`, `is_atom`, `is_list`, `is_tuple`, `is_boolean`, `is_pid`, `is_function`, `is_binary`, `is_map`

**Conversion**: `atom_to_list`, `list_to_atom`, `integer_to_list`, `list_to_integer`, `list_to_tuple`, `tuple_to_list`, `float_to_list`, `integer_to_binary`, `atom_to_binary`

**List ops**: `hd`, `tl`, `length`, `element`, `tuple_size`, `++`, `--`, `setelement`

**Maps**: `maps:get`, `maps:put`, `maps:is_key`, `maps:keys`, `maps:values`, `maps:size`, `maps:to_list`, `maps:from_list`, `maps:find`, `maps:remove`, `maps:merge`, `map_size`

**Lists module**: `lists:reverse`, `lists:member`, `lists:keyfind`, `lists:keymember`, `lists:keysearch`

**Process**: `self`, `spawn/3`, `send/2`, `register/2`, `whereis/1`, `put/2`, `get/1`, `process_flag/2`, `node/0`

**I/O**: `erlang:display/1`, `io:format/1,2`

## Limitations

- No garbage collection (fixed 64K word heap per process)
- No binary pattern matching (bs_start_match, bs_get_integer, etc.)
- No full OTP library — only built-in BIFs listed above
- Fixed-size tables (4096 atoms, 64 modules, 1024 processes)
- No distribution, no ports, no NIFs
- No full exception handling (basic try/catch only)
