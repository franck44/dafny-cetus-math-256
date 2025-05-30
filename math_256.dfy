/**
  *  Provides a mechanical proof of the correctness of the `checked_shlwv` function,
  *  which performs a left shift operation on a 256-bit unsigned integer.
  */
module math_u256 {

  // Use some Dafny standard libraries for definitions & proofs

  // Definition of 2^n (Power2(m))
  import opened Std.Arithmetic.Power2
  // Use inequality (monotonicity)
  import opened Std.Arithmetic.Mul
  // Use lemma Lemma2To64();
  import opened Std.BoundedInts

  /**
    * Performs a left shift by 64 bits on a 256-bit unsigned integer.
    * The function checks for overflow by testing if the input is larger than or equal to 2^192.
    * If overflow occurs, returns (0, true), otherwise returns (n << 64, false).
    *
    * @param n A 256-bit unsigned integer to be shifted left
    * @returns A tuple (r.0, r.1) where:
    *   - r.0 is the shifted value if no overflow, 0 otherwise
    *   - r.1 is true iff n * 2^64 >= 2^256
    */
  function checked_shlwv(n: bv256): (r: (bv256, bool))
    // false indicates not overflow and n << 64 is equal to n as nat * Pow2(256)
    ensures !r.1 ==> r.0 as nat == n as nat * Pow2(64) < Pow2(256)
    // true indicates overflow if we compute n >> 64 as n as nat * Pow2(64)
    // does not fit within a bv256
    ensures r.1 ==> r.0 == 0 && n as nat * Pow2(64) >= Pow2(256)
    // Summary as an iff condition
    ensures !r.1 <==>  n as nat * Pow2(64) < Pow2(256)
  {
    var mask := (1 as bv256 << 192 as bv8);
    calc {
      mask as nat;
      (1 as bv256 << 192 as bv8) as nat;
      { Bv2562Pow2(192 as bv8); }
      Pow2(192);
    }
    if (n >= mask) then
      assert n as nat >= Pow2(192);
      LemmaHelperShiftLeft64LargerThanPow2_192(n);
      assert n as nat * Pow2(64) >= Pow2(256);
      (0, true)
    else
      assert n as nat < Pow2(192);
      LemmaHelperShiftLeft64LessThanPow2_192(n);
      assert  (n << 64) as nat == n as nat * Pow2(64) < Pow2(256);
      (n << 64, false)
  }

  //---------------------------------------------------------------
  // Some useful lemmas
  //---------------------------------------------------------------

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