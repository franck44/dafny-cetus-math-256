
This repository contains a **formal specification** and **correctness proof** of the `checked_shlw`, that was the root cause of the [Cetus Protocol incident](https://cetusprotocol.notion.site/Cetus-Incident-Report-May-22-2025-Attack-Disclosure-1ff1dbf3ac8680d7a98de6158597d416) on May 22, 2025.
The incident involved a vulnerability in the function `checked_shlw` function, which led to a significant loss of funds (~USD230M). The formal specification and proof aim to provide a clear understanding of the function's behavior and ensure its correctness.

## Overview


The function [checked_shlw](https://github.com/CetusProtocol/integer-mate/blob/06660f704c4ac1d443ab62346a46b5b60d49df33/sui/sources/math_u256.move#L18) is part of the math library [integer mate](https://github.com/CetusProtocol/integer-mate) ("libary" :smile: on the Cetus repo ...) and is implemented in the module `math_u256`.

The function does not have a documentation, nor comments, and apparently it is not unit tested (even after the fix from last week). 

The "fixes" were applied to the Sui and Aptos versions of the library via 2 PRs:

- [PR #7:](https://github.com/CetusProtocol/integer-mate/pull/7/files) fixes the comparison of the mask value and the input, `n > mask` becomes `n >= mask`.
- [PR #6:](https://github.com/CetusProtocol/integer-mate/pull/6/files) the value of the mask `0xffffffffffffffff << 192` was wrong and was changed to `1 << 192`.

The "fixed code" is as follows:

```rust
public fun checked_shlw(n: u256): (u256, bool) {
    let mask = 1 << 192;
    if (n >= mask) {
        (0, true)
    } else {
        ((n << 64), false)
    }
}
```

The intention seems to be that the function `checked_shlw` should shift the input `n` left by 64 bits, but only if the value of `n` is less than `1 << 192`, i.e doe snot overflow. If `n` is greater than or equal to `1 << 192`, the function returns `(0, true)` indicating an overflow.


## Why is it important to have a formal specification and proof?

Although some changes were made to fix the code, there is still no documentation, nor tests for this function. 
There may be other issues in the code that were not addressed by the PRs above, and the formal specification and proof can help identify and address these issues.


Providing a formal specification has the advantage of being a clear and unambiguous description of the function's behavior, which can be used to verify its correctness.

There is also another function `div_round` that may result in an overflow (returns `p + 1` and `p: u256`). 

```rust
public fun div_round(num: u256, denom: u256, round_up: bool): u256 {
    let p = num / denom;
    if (round_up && ((p * denom) != num)) {
        // make sure no verflow here
        p + 1
    } else {
        p
    }
}
```

## Formal specification and Proof
We provide a formal specification and correctness proof for both `checked_shlw` and `div_round`.
The specification and verification uses [Dafny](https://dafny.org/), a programming language and verification tool that allows us to write specifications and proofs in a formal and machine-checkable way.

The Dafny proof is valid on the MOve code as the code does not contain any Move specific constructs, and we can use a *shallow embedding* of the Move code into Dafny.
A *shallow embedding* means that we can directly translate the Move code into Dafny code, without having to define a separate semantics (deep embedding) for the Move language.
As an example, an `if-then-else` statement in Move can be directly translated to an `if-then-else` statement in Dafny as they have the same semantics.

## How is the proof structured?

The proof uses a mix of SMT-theories including `bit-vectors` and `integers`, and leverages the [Dafny standard libraries](https://github.com/dafny-lang/libraries) to help with useful lemmas that are necessary to prove the correctness of the function.


The main components of the proof for `checked_shlw` are:
- some folks theorems relating shifts and poers of 2, e.g. `1 << n` to `2^n`. 
- some simple verified calculations to prove the correctness of the function `chedked_shlw`.
- the post conditions of the function `checked_shlw` that precisely capture the behavior of the function.

For `div_roundup`, the specification captures the precise behavior of the function, and the proof shows that the function satisfies the specification.

## How to run the proof?
To run the proof, you need to have Dafny installed on your machine.Follow the instructions on the [Dafny github](https://github.com/dafny-lang/dafny) to install it.

Once you have Dafny installed, pull this repo and check the code either using VsCode and the Dafny plugin or using the command line.

```zsh
> git clone https://github.com/franck44/dafny-cetus-math-256
> cd dafny-cetus-math-256
> dafny verify --standard-libraries math_u256.dfy
> dafny-cetus-math-256 git:(main) ✗ dafny verify --standard-libraries math_256.dfy

> Dafny program verifier finished with 9 verified, 0 errors
```

## How much work is it to write ther proof?
One person, arguably with some experience in formal verification and Dafny. 
A few hours. Cost is far less than USD230M.
