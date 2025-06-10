/**
  *  Provide some helper lemmas to reason about
  *  integers and bit-vectors.
  */
module MathBVHelpers {

  // Use some Dafny standard libraries for definitions & proofs

  // Definition of 2^n (Power2(m))
  import opened Std.Arithmetic.Power2
  // Use inequality (monotonicity)
  import opened Std.Arithmetic.Mul
  // Use lemma Lemma2To64();
  import opened Std.BoundedInts
  // import values of masks.
  import opened MaxConstants

  // define the u256 type
  newtype u256 = x: int | 0 <= x < TWO_TO_THE_256

  //---------------------------------------------------------------
  // Some useful lemmas
  //---------------------------------------------------------------

  /**
    * Axiom proving that converting a 128-bit bitvector to int and back preserves the value.
    * Also ensures that the int value is less than 2^128.
    *
    * @param a A 128-bit bitvector
    * @ensures Converting a to int and back to bv128 yields the original value
    * @ensures The int value is less than 2^128
    *
    * @note In the SMT-theories mixing bv and int, the conversions
    * are uninterpreted and not precise enough. This axiom provides 
    * a more precise relation between bv128 and their int values.
    */
  lemma {:axiom} as_int_as_bv128(a: bv128)
    ensures (a as int) as bv128 == a
    ensures (a as int) < Pow2(128)

  /**
    * Axiom proving that converting a uint128 to bv128 and back preserves the value.
    *
    * @param a A 128-bit unsigned integer
    * @ensures Converting a to bv128 and back to uint128 yields the original value
    *
    * @note In the SMT-theories mixing bv and int, the conversions
    * are uninterpreted and not precise enough. This axiom provides 
    * a more precise relation between uint128 and their bv128 values.
    */
  lemma {:axiom} as_bv128_as_uint128(a: uint128)
    ensures (a as bv128) as uint128 == a

  /**
    * Prove if n is small enough, < Pow2(192), the shift left does not
    * overflow.
    * This lemma is used in the proof of checked_shlwv.
    *
    * @param n A 256-bit unsigned integer
    * @requires The result of n as nat * 2^64 must be less than 2^256 
    * @ensures no overflow: the result of the bit shift operation n << 64 is equal to n as nat * 2^64
    */
  lemma LemmaHelperShiftLeft64LessThanPow2_192(n: bv256)
    requires n as nat < Pow2(192)
    ensures (n << 64) as nat == n as nat * Pow2(64) < Pow2(256)
  {
    // Bring constants Pow2(k) == TWO_TO_THE_k, k=64, 256 into scope
    Lemma2To256();
    // inequality n as nat * Pow2(64) < Pow2(256)
    calc ==> {
      n as nat <  Pow2(192);
      { Mul.LemmaMulStrictInequality(n as nat, Pow2(192), Pow2(64));}
      (n as nat) * Pow2(64) < Pow2(192) * Pow2(64);
      {  Power.LemmaPowAdds(2, 192 ,64);}
      (n as nat) * Pow2(64) < Pow2(256);
    }
    //  (n << 64) as nat == n as nat * Pow2(64)
    calc {
      n as nat * Pow2(64) ;
      n as nat * TWO_TO_THE_64;
      (n << 64) as nat;
    }
  }

  /**
    * Prove if n is large enough (>= 2^192), shifting left by 64 bits will
    * result in overflow.
    * This lemma is used in the proof of checked_shlwv.
    *
    * @param n A 256-bit unsigned integer
    * @requires n must be greater than or equal to 2^192
    * @ensures The result of n as nat * 2^64 must be greater than or equal to 2^256 (overflow)
    */
  lemma LemmaHelperShiftLeft64LargerThanPow2_192(n:bv256)
    requires n as nat >= Pow2(192)
    ensures n as nat * Pow2(64) >= Pow2(256)
  {
    calc ==> {
      Pow2(192) <= n as nat;
      { Mul.LemmaMulInequality(Pow2(192), n as nat, Pow2(64)); }
      Pow2(192) * Pow2(64) <= n as nat * Pow2(64);
      { Power.LemmaPowAdds(2, 192 ,64); }
      Pow2(256) <= n as nat * Pow2(64);
    }
  }

  /**
    * Equality between 1 << l and 2^l.
    * 
    * @param l The amount to shift left
    * @ensures 1 << l == 2^l
    */
  lemma Bv2562Pow2(l: bv8)
    ensures (1 as bv256 << l) as nat == Pow2(l as nat)
  {
    // Base case l == 0 is proved automatically by Dafny
    if l > 0 {
      Bv2562Pow2(l - 1) ;
    }
  }

  /**
    * Equalities between Pow2(64), Pow2(256) and the corresponding constants.
    */
  lemma Lemma2To256()
    ensures Pow2(64) == TWO_TO_THE_64
    ensures Pow2(256) == TWO_TO_THE_256
  {
    Lemma2To64();
    Power.LemmaPowAdds(2, 64 ,64);  // 2^64 * 2^64 == 2^{64 + 64} = 2^128
    assert Pow2(128) == TWO_TO_THE_64 * TWO_TO_THE_64;
    Power.LemmaPowAdds(2, 128 ,128);  // 2^128 * 2^128 == 2^{128 + 128} = 2^256
    assert Pow2(256) == TWO_TO_THE_128 * TWO_TO_THE_128;
  }
}