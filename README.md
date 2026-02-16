# beam.zig

A minimalist BEAM virtual machine written in Zig. Single-file implementation (~2300 lines) that loads and executes `.beam` files compiled by `erlc`.

## Features

- Tagged u64 term representation (integers, atoms, lists, tuples, pids)
- BEAM file loader with IFF chunk parsing (AtU8, Code, ImpT, ExpT, LitT, FunT)
- Compact term encoding decoder
- External Term Format (ETF) literal decoder
- Switch-dispatch execution engine (~50 opcodes)
- Round-robin process scheduler
- Message passing between processes
- Pattern matching (select_val, select_tuple_arity, is_tagged_tuple)
- BIFs: arithmetic, comparison, type checks, list ops, erlang:display, erlang:spawn/3, io:format

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
cd test && erlc hello.erl fac.erl fib.erl list_ops.erl spawn_test.erl && cd ..

# Run all tests
./zig-out/bin/beam test/hello.beam       # hello, 42, {ok,[1,2,3]}
./zig-out/bin/beam test/fac.beam         # 3628800
./zig-out/bin/beam test/fib.beam         # 6765
./zig-out/bin/beam test/list_ops.beam    # 15, [5,4,3,2,1]
./zig-out/bin/beam test/spawn_test.beam  # done, {hello,world}
```

## Limitations

- No garbage collection (fixed 64K word heap per process)
- No binary/map support
- No full OTP library — only a handful of BIFs
- Fixed-size tables (4096 atoms, 64 modules, 1024 processes)
- No distribution, no ports, no NIFs
