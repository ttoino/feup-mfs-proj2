# FEUP-MFS-PROJ2

Second project for the MFS course unit at FEUP.

The goal of this project was to implement and formally verify an algorithm to find the k smallest elements in an array using Dafny, a programming language with built-in formal verification capabilities.

## Project Structure

- `find_k_smallest.dfy` - Main algorithm implementation with formal specifications
- `Find.dfy` - Helper functions for finding elements
- `Partition.dfy` - Partition algorithm implementation
- `Io.dfy` - I/O handling specifications
- `IoNative.cs` - Native C# I/O implementation

## Algorithm

The implementation uses a partitioning approach to find the k smallest elements:

1. **Partitioning**: Similar to QuickSort's partition, rearranges elements around a pivot
2. **Selection**: Recursively narrows down to find the k smallest elements
3. **Verification**: Pre-conditions, post-conditions, and loop invariants ensure correctness

## Key Features

- Formal specification of pre-conditions and post-conditions
- Loop invariants for verification
- Ghost variables for tracking algorithm state
- Native I/O for practical usage

## Running

To verify the implementation:

```bash
dafny find_k_smallest.dfy
```

To compile and run (requires .NET):

```bash
dafny build --target:cs find_k_smallest.dfy
./find_k_smallest
```

## Unit info

- **Name**: Métodos Formais para Sistemas Críticos (Formal Methods for Critical Systems)
- **Date**: Year 1, Semester 2, 2023/24
- [**More info**](https://sigarra.up.pt/feup/ucurr_geral.ficha_uc_view?pv_ocorrencia_id=522746)

## Disclaimer

This repository (and all others with the name format `feup-*`) are for archival and educational purposes only.

If you don't understand some part of the code or anything else in this repo, feel free to ask (although I may not understand it myself anymore).

Keep in mind that this repo is public. If you copy any code and use it in your school projects you may be flagged for plagiarism by automated tools.
