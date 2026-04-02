# The Cryptographic Layer of Biometric Authentication

## Requirements
- Rust 1.70+

## Build
`cargo build --release`

## Run
### Correctness demo (k=8)
`cargo run --release -- run 8`

### Timing benchmarks
`cargo run --release -- bench`

### Size report
`cargo run --release -- sizes`

### Expected output for Correctness demo
```
b  = [1, 1, 1, 1, 1, 1, 0, 1]
b' = [1, 0, 0, 1, 0, 1, 1, 0]
True HD = 5

--- PiH ---
PiH  HD = 5

--- PiHC ---
PiHC HD = 5
```

## Reproducing paper results
The benchmarks in Table 1 were run on:
- CPU: Apple-M1 Pro
- RAM: 32 GB
- OS: macOS 15.6.1
- Rust: 1.94.0

## Acknowledgements
This implementation was developed with the assistance of [Claude](https://claude.ai) (Anthropic), an AI coding assistant.
All cryptographic logic and results were verified by the authors.
