--------------------------------------------------------------------
--------------------------------------------------------------------
----- TEST #1
--------------------------------------------------------------------
--------------------------------------------------------------------
TEST ///
assert(bitXor(5,3) == 6)
assert(bitXor(10,12) == 6)
assert(bitXor(0,3) == 3)
assert(bitXor(7,7) == 0)
///


--------------------------------------------------------------------
--------------------------------------------------------------------
----- TEST #2
--------------------------------------------------------------------
--------------------------------------------------------------------
TEST ///
assert(permutationSign({0, 1}) == 0)
assert(permutationSign({1,0}) == 1)
assert(permutationSign({2, 0, 4, 3, 1}) == 1)
assert(permutationSign({0, 2, 4, 3, 1}) == 0)
--
H1 = new MutableHashTable from {(0,0), (1,1)};
L1 = new MutableList from {0,1};
assert(permutationSign(H1,L1) == 0)
--
H2 = new MutableHashTable from {(0,1), (1,0)};
L2 = new MutableList from {0,1};
assert(permutationSign(H2,L2) == 1)
--
H3 = new MutableHashTable from {(0,2), (1,0), (2,4), (3,3), (4,1)};
L3 = new MutableList from {0,1,2,3,4};
assert(permutationSign(H3,L3) == 1)
///


--------------------------------------------------------------------
--------------------------------------------------------------------
----- TEST #3
--------------------------------------------------------------------
--------------------------------------------------------------------
TEST ///
assert(isOdd({0, 1}) == false)
assert(isOdd({1,0}) == true)
assert(isOdd({2, 0, 4, 3, 1}) == true)
assert(isOdd({0, 2, 4, 3, 1}) == false)
--
assert(isEven({0, 1}) == true)
assert(isEven({1,0}) == false)
assert(isEven({2, 0, 4, 3, 1}) == false)
assert(isEven({0, 2, 4, 3, 1}) == true)
///


--------------------------------------------------------------------
--------------------------------------------------------------------
----- TEST #4
--------------------------------------------------------------------
--------------------------------------------------------------------
TEST ///
assert(bitLength(3) == 2)
assert(bitLength(64) == 7)
--
assert(leadingBit(3) == 1)
assert(leadingBit(64) == 6)
///

--------------------------------------------------------------------
--------------------------------------------------------------------
----- TEST #5
--------------------------------------------------------------------
--------------------------------------------------------------------
TEST ///
assert(gussianEliminationBinaryList({1, 2, 3, 4}) == (3, {1, 2, 4}))
assert(gussianEliminationBinaryList({1, 2, 4, 7}) == (3, {1, 2, 4}))
--
-- v = 7 (binary 111), pivots cover bits 0 and 1
-- 7 XOR 1 XOR 2 = 4
assert(gussianEliminationBinaryList(7, {{0, 1}, {1, 2}}) == 4)
assert(gussianEliminationBinaryList(0, {{0, 1}, {1, 2}}) == 0)
-- pivots: bit 0 -> 1 (binary 01), bit 1 -> 2 (binary 10)
-- v = 3 (binary 11) should reduce to 0 via XOR with both pivots
assert(gussianEliminationBinaryList(3, {{0, 1}, {1, 2}}) == 0)
--
assert(isIndependent({1, 2, 4, 8}) == true)
assert(isIndependent({5}) == true)
assert(isIndependent({3, 3}) == false)
///


--------------------------------------------------------------------
--------------------------------------------------------------------
----- TEST #6
--------------------------------------------------------------------
--------------------------------------------------------------------
TEST ///
--------------------------------------------------------------------
-- TEST EXAMPLES
--------------------------------------------------------------------
-- Encoding convention: integer n encodes a binary vector whose
-- bits are the coordinates over GF(2).
--
--   7 = 111,  5 = 101,  3 = 011,  6 = 110
--   4 = 100,  2 = 010,  1 = 001

--------------------------------------------------------------------
-- Test 0: empty list
--------------------------------------------------------------------
assert( greedyBinaryBasis({}) == {} )

--------------------------------------------------------------------
-- Test 1: single nonzero element
--------------------------------------------------------------------
assert( greedyBinaryBasis({5}) == {5} )
--------------------------------------------------------------------
-- Test 2: standard basis vectors — all independent
--   4=100, 2=010, 1=001  →  should keep all three
--------------------------------------------------------------------
assert( greedyBinaryBasis({4, 2, 1}) == {4, 2, 1} )

--------------------------------------------------------------------
-- Test 3: three independent, one dependent
--   7=111, 5=101, 3=011, 6=110
--   Note: 6 = 5 xor 3, so {7,5,3} spans and 6 is redundant
--   Trace:
--     7 → vRed=7, pivot@bit2 = 7         kept
--     5 → vRed = 5 xor 7 = 2, pivot@bit1 = 2   kept
--     3 → vRed = 3 xor 2 = 1, pivot@bit0 = 1   kept
--     6 → vRed = 6 xor 7 = 1, then 1 xor 1 = 0   skipped
--------------------------------------------------------------------
assert( greedyBinaryBasis({7, 5, 3, 6}) == {7, 5, 3} )

--------------------------------------------------------------------
-- Test 4: all duplicates
--   Every copy after the first reduces to 0
--------------------------------------------------------------------
assert( greedyBinaryBasis({3, 3, 3}) == {3} )

--------------------------------------------------------------------
-- Test 5: early-stop variant — request 2 out of 3 independent
--------------------------------------------------------------------
assert( greedyBinaryBasis(2, {4, 2, 1}) == {4, 2} )

--------------------------------------------------------------------
-- Test 6: early-stop when list has fewer than k independent vectors
--   {3, 3, 3} has only 1 independent vector, but we ask for k=2
--   Should return what it found, not null.
--------------------------------------------------------------------
result6 := greedyBinaryBasis(2, {3, 3, 3});
assert( result6 == {3} )

--------------------------------------------------------------------
-- Test 7: zero in the input list — should be silently skipped
--------------------------------------------------------------------
assert( greedyBinaryBasis({0, 5, 0, 3}) == {5, 3} )
///


--------------------------------------------------------------------
--------------------------------------------------------------------
----- TEST #7
--------------------------------------------------------------------
--------------------------------------------------------------------
TEST ///
-- Encoding: integer bits are GF(2) coordinates.
--   v = sum v_i 2^i     selects which basis elements to XOR
--   B = {b0, b1, ...}   the "columns"
--   result = XOR of b_i for every set bit i of v
--------------------------------------------------------------------
--------------------------------------------------------------------
-- Test 0: zero selector — no columns selected, result is 0
--------------------------------------------------------------------
assert( multiplyBinaryList(0, {7, 5, 3}) == 0 )
--------------------------------------------------------------------
-- Test 1: v selects only the first column
--   v = 1 = ...001  →  picks B#0 = 7
--------------------------------------------------------------------
assert( multiplyBinaryList(1, {7, 5, 3}) == 7 )
--------------------------------------------------------------------
-- Test 2: v selects only the second column
--   v = 2 = ...010  →  picks B#1 = 5
--------------------------------------------------------------------
assert( multiplyBinaryList(2, {7, 5, 3}) == 5 )
--------------------------------------------------------------------
-- Test 3: v selects columns 0 and 1
--   v = 3 = ...011  →  7 xor 5 = 2
--   7 = 111, 5 = 101  →  xor = 010 = 2
--------------------------------------------------------------------
assert( multiplyBinaryList(3, {7, 5, 3}) == 2 )
--------------------------------------------------------------------
-- Test 4: v selects all three columns
--   v = 7 = ...111  →  7 xor 5 xor 3
--   111 xor 101 = 010, then 010 xor 011 = 001 = 1
--------------------------------------------------------------------
assert( multiplyBinaryList(7, {7, 5, 3}) == 1 )
--------------------------------------------------------------------
-- Test 5: identity-like basis {4,2,1} = standard basis vectors
--   v selects a subset, so result should just be v
--   v = 5 = 101  →  picks B#0=4(100) and B#2=1(001)  →  xor = 101 = 5
--------------------------------------------------------------------
assert( multiplyBinaryList(5, {4, 2, 1}) == 5 )
///


--------------------------------------------------------------------
--------------------------------------------------------------------
----- TEST #8
--------------------------------------------------------------------
--------------------------------------------------------------------
TEST ///
------------------------------------------------------------
-- Test 1: i = 0  (base case, k only takes value 0)
-- img = B#0 = 5, src = 1 << 0 = 1
-- No inner loop iterations since i-1 < 0
------------------------------------------------------------
B1 = {5};
pos1 = new MutableHashTable from {5 => 10};
srcL1 = new MutableHashTable from {1 => 100};

(ok1, pairs1) = verifyPartialMap(0, B1, pos1, srcL1);
assert(ok1 == true);
assert(pairs1 == {(100, 10)});

------------------------------------------------------------
-- Test 2: i = 1  (k in {0, 1})
-- k=0: img = B#1 = 3,        src = 2    (binary 10)
-- k=1: img = B#1 xor B#0 = 3 xor 5 = 6, src = 2 xor 1 = 3 (binary 11)
------------------------------------------------------------
B2 = {5, 3};
pos2 = new MutableHashTable from {3 => 20, 6 => 21};
srcL2 = new MutableHashTable from {2 => 200, 3 => 201};

(ok2, pairs2) = verifyPartialMap(1, B2, pos2, srcL2);
assert(ok2 == true);
assert(#pairs2 == 2);
assert(pairs2#0 == (200, 20));   -- k=0
assert(pairs2#1 == (201, 21));   -- k=1

------------------------------------------------------------
-- Test 3: Failure case — image not found in posTable
-- i = 1, k=0 gives img = B#1 = 7, which IS in posTable
-- k=1 gives img = 7 xor 5 = 2, which is NOT in posTable
------------------------------------------------------------
B3 = {5, 7};
pos3 = new MutableHashTable from {7 => 30};  -- missing entry for 2
srcL3 = new MutableHashTable from {2 => 300, 3 => 301};

(ok3, pairs3) = verifyPartialMap(1, B3, pos3, srcL3);
assert(ok3 == false);
assert(pairs3 == {});
///
