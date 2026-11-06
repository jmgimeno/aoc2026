set dotenv-load

# Build the 2026 solutions; this also checks their #guard tests
build:
    lake build

# Run the tests that read input files
test:
    lake test

# Build the 2025 reference examples, including their proofs
examples:
    lake build Examples2025

# Print the answers of a day, for example: just run day01
run day:
    lake exe aoc2026 {{day}}

# Download the input of a day, for example: just download day01
download day:
    lake exe downloader {{day}}
