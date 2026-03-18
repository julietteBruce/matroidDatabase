needsPackage "Matroids";
needsPackage "SpechtModule";

--
-- ============================================================
-- Exact odd automorphism test for a simple binary matroid
-- represented by Fripertinger/Wild binary column labels.
--
-- Mathematical fact used:
--   If S is a set of distinct nonzero vectors in GF(2)^k representing
--   a simple binary matroid, then every matroid automorphism is induced
--   by a unique invertible linear map T in GL(k,2).
--
-- Therefore it is enough to:
--   1. choose one ordered basis B of S;
--   2. try every ordered independent k-tuple Bim in S as the image of B;
--   3. extend linearly using coordinates relative to B;
--   4. test whether T(S) = S;
--   5. test whether the induced permutation on the sorted ground set is odd.
--
-- This is exact.  It does NOT rely on 3-connectedness.
-- Connectedness is not checked, because it is not needed for correctness.
-- ============================================================

--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Bitwise xor of ingeter vectors, compares each
----- digit of the two numbers binary expansion and returns 1
----- where the digist differ, 0 where they're the same.
----- e.g. 5 = 0101, 3 = 0011 then bitXor(5,3) = 6
----- (0 xOr 0) (1 xOr 0) (0 xOr 1) (1 xOr 1)  = 0110 = 6
-----
----- The key for us is that this gives a fast way to add vectors
----- in (F_2)^k without having to create vectors:
----- e.g. 5 = (0,1,0,1) and 3 = (0,0,1,1) in (F_2)^4 then
----- (0,1,0,1) + (0,0,1,1) = (0,1,1,0)
----- which we may think of as being represented by 6. 
--------------------------------------------------------------------
--------------------------------------------------------------------
bitXor = method();
bitXor (ZZ, ZZ) := (a,b) -> (
    a ^^ b
);

bitXor(5,3) == 6
bitXor(10,12) == 6
bitXor(0,3) == 3
bitXor(7,7) == 0

--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Given a list  of integers 0 to n-1 repersenting
----- a premuation of 0 to n-1 this computes the sign as 0 (even)
----- or 1 (odd) using cycle decomposition.
--------------------------------------------------------------------
--------------------------------------------------------------------
permutationSign = method();
permutationSign (List) := (L) -> (
    n := #L;
    visited := new MutableList from (n : false);
    evenCycles := 0; 
    for i from 0 to n-1 do (
	if visited#i == false then (
	    cycleLength := 0;
	    j := i;
	    while visited#j == false do (
		visited#j = true;
		cycleLength = cycleLength + 1;
		j = L#j;
		);
	    if cycleLength % 2 == 0 then evenCycles = evenCycles + 1;
	    );
	);
    evenCycles % 2 
    )

permutationSign (MutableHashTable, MutableList) := (P, I) -> (   
    visited := new MutableHashTable;
    numCycles := 0;
    for i in I do (
	if not visited#?i then (
	    numCycles = numCycles + 1;
	    curPos := i;
	    while not visited#?curPos do (
		visited#curPos = true;
		curPos = P#curPos;
		);
	    );
	);
    (#I - numCycles) % 2 
    )

permutationSign({0, 1}) == 0
permutationSign({1,0}) == 1
permutationSign({2, 0, 4, 3, 1}) == 1
permutationSign({0, 2, 4, 3, 1}) == 0
--
H1 = new MutableHashTable from {(0,0), (1,1)}
L1 = new MutableList from {0,1}
permutationSign(H1,L1) == 0

H2 = new MutableHashTable from {(0,1), (1,0)}
L2 = new MutableList from {0,1}
permutationSign(H2,L2) == 1

H3 = new MutableHashTable from {(0,2), (1,0), (2,4), (3,3), (4,1)}
L3 = new MutableList from {0,1,2,3,4}
permutationSign(H3,L3) == 1

isOdd = method();
isOdd (List) := (L) -> (
    permutationSign(L) == 1
    )

isOdd({0, 1}) == false
isOdd({1,0}) == true
isOdd({2, 0, 4, 3, 1}) == true
isOdd({0, 2, 4, 3, 1}) == false

isEven = method();
isEven (List) := (L) -> (
    permutationSign(L) == 0
    )

isEven({0, 1}) == true
isEven({1,0}) == false
isEven({2, 0, 4, 3, 1}) == false
isEven({0, 2, 4, 3, 1}) == true




--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Returns the number of digits of n written in
----- binary, i.e., smallest i such that 2^i > n.
--------------------------------------------------------------------
--------------------------------------------------------------------

bitLength = method();
bitLength (ZZ) := (n) -> (
    if n < 0 then error "expect positive integer";
    if n == 0 then 1
    else (
	i := 0;
	while n > 0 do (
	    n = n // 2;
	    i = i + 1;
	    );
	i
    )
)

bitLength(3) == 2
bitLength(64) == 7
--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Returns the last position of non-zero digit
----- in the binary representation of n.
--------------------------------------------------------------------
--------------------------------------------------------------------
leadingBit = method();
leadingBit (ZZ) := (n) -> (
    bitLength(n) - 1
    )

leadingBit(3) == 1
leadingBit(64) == 6
--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Does Guassian elimination on a binary list
----- using bit operations without making matrix
--------------------------------------------------------------------
--------------------------------------------------------------------
gussianEliminationBinaryList = method();
gussianEliminationBinaryList (List) := (L) -> (
    pivotHash := new MutableHashTable;
    r := 0;
    --
    for v in L do (
	vRed := v;
	--
	if vRed == 0 then continue;
	--
	-- tries to reduce the column represented by v with existing pivots
	while vRed != 0 and pivotHash#?(leadingBit(vRed)) do (
	    vRed = bitXor(vRed, pivotHash#(leadingBit(vRed)));
	    );
	--
	-- if vRed != 0 then bitLength(vRed) is not in pivoHash so we need new pivot
	if vRed != 0 then (
	    newPivot := leadingBit(vRed);
	    --
	    -- back substitution
	    for j in keys(pivotHash) do (
		if ((pivotHash#j >> newPivot) & 1) == 1 then (
			pivotHash#j = bitXor(pivotHash#j, vRed);
			);
		);
	    -- update pivots and rank counter
	    pivotHash#newPivot = vRed;
	    r = r + 1;
            );
	);
    (r, values pivotHash)
    )

gussianEliminationBinaryList({1, 2, 3, 4}) == (3, {1, 2, 4})
gussianEliminationBinaryList({1, 2, 4, 7}) == (3, {1, 2, 4})


gussianEliminationBinaryList (ZZ, List) := (v, pivotList) -> (
    for piv in pivotList do (
	pivotCol := piv#0;
	pivotVec := piv#1;
	if (v >> pivotCol) % 2 == 1 then v = bitXor(v, pivotVec)
	);
    v
    )

-- v = 7 (binary 111), pivots cover bits 0 and 1
-- 7 XOR 1 XOR 2 = 4
gussianEliminationBinaryList(7, {{0, 1}, {1, 2}}) == 4
gussianEliminationBinaryList(0, {{0, 1}, {1, 2}}) == 0
-- pivots: bit 0 -> 1 (binary 01), bit 1 -> 2 (binary 10)
-- v = 3 (binary 11) should reduce to 0 via XOR with both pivots
assert(gussianEliminationBinaryList(3, {{0, 1}, {1, 2}}) == 0)

isIndependent = (L) -> (
    (gussianEliminationBinaryList(L))#0 == #L
    )

isIndependent({1, 2, 4, 8}) == true
isIndependent({5}) == true
isIndependent({3, 3}) == false
--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Uses greedy algorithm to find a subset of a
----- a binary list that is a basis for the span of the list.
--------------------------------------------------------------------
--------------------------------------------------------------------
greedyBinaryBasis = method();
greedyBinaryBasis (List) := (L) -> (
    pivotHash := new MutableHashTable;
    basisList := new MutableList from {};
    ind := 0;
    for v in L do (
	vRed := v;
       	--
	-- tries to reduce the column represented by v with existing pivots
	while vRed != 0 and pivotHash#?(leadingBit(vRed)) do (
	    vRed = bitXor(vRed, pivotHash#(leadingBit(vRed)));
	    );
	--
	-- this means v not in span yet
	if vRed != 0 then (
	    pivotHash#(leadingBit(vRed)) = vRed;
	    -- store original vector *not* the reduced one
	    basisList#ind = v;
            ind = ind + 1;
        );
	);
    toList(basisList)
    )

greedyBinaryBasis (ZZ, List) := (k, L) -> (
    pivotHash := new MutableHashTable;
    basisList := new MutableList from {};
    ind := 0;
    for v in L do (
	vRed := v;
       	--
	-- tries to reduce the column represented by v with existing pivots
	while vRed != 0 and pivotHash#?(leadingBit(vRed)) do (
	    vRed = bitXor(vRed, pivotHash#(leadingBit(vRed)));
	    );
	--
	-- this means v not in span yet
	if vRed != 0 then (
	    pivotHash#(leadingBit(vRed)) = vRed;
	    -- store original vector *not* the reduced one
            basisList#ind = v;
            ind = ind + 1;
        );
	if #basisList == k then return toList(basisList)
	);
    return error "vectors do not span k-dim space.";
    )



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


--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Given a vector v in (Z/2Z)^k and a binary list
----- B this essentally does B*v without matrices:
----- v = sum v_i 2^i and B = {b1, b2, ..., bt} then 
----- output is sum v_i*b_i
--------------------------------------------------------------------
----------------------------------------------------------------------
multiplyBinaryList = method();
multiplyBinaryList (ZZ, List) := (v, B) -> (
    n := 0;
    for i from 0 to (#B - 1) do (
	if (((v >> i) & 1) == 1) then (n = bitXor(n, B#i));
	);
    n
    )

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



verifyPartialMap = method();
verifyPartialMap (ZZ, List, MutableHashTable, MutableHashTable) :=  (i, B, posTable, srcLookup) -> (
    newPairs := new MutableList;
    numPrev := 1 << i;
    for k from 0 to (numPrev - 1) do (
	img := B#i;
	src := (1 << i);
	for j from 0 to (i - 1) do (
	    if  (k >> j) % 2 == 1 then (
		img = bitXor(img, B#j);
		src = bitXor(src, 1 << j);
		);
	    );
	if not posTable#?img then return (false, {});
	--
	dstID := posTable#img;
	srcID := if srcLookup#?src then srcLookup#src
                 else error("no source found for bit pattern " | toString src);
        newPairs#(#newPairs) = (srcID, dstID);
	);
    (true, toList newPairs)
    )


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



membershipTable = method();
membershipTable (List) := (L) -> (
    membTable := new MutableHashTable;
    for x in L do membTable#x = true;
    membTable
    )

-- WARNING ONLY WORKS FOR NON-DUPLICATES
positionTable = method();
positionTable (List) := (L) -> (
    posTable := new MutableHashTable;
    for i from 0 to (#L - 1) do (posTable#(L#i) = i);
    posTable
    )


-- Coordinate table relative to an ordered basis B.
-- T#x = mask such that x = evalMaskGF2(mask,B).
coordinateTable = method();
coordinateTable (ZZ, List) := (k, B) -> (
    if #B != k then error "Basis has wrong length";
    if not (isIndependent(B,k)) then error "B is not independent";
    --
    T := new MutableHashTable;
    --
    for v from 0 to (2^k - 1) do (
        x := multiplyBinaryList(v,B);
        if T#?x then error "coordinateTableGF2: duplicate vector found; B is not a basis";
        T#x = v;
    );
    --
    T
);

hasOddAut = method((Options => {Validate => false});
hasOddAut (ZZ, List) := opts -> (k, L) -> (
    -- optional validation step, which can be skipped for speed
    if opts.Validate == true then (
	validateBinaryMatroidData(L)
	);
    -- basic set-up
    n := #L;  -- size of ground set
    B := greedyBinaryBasis(k, L); -- basis for span of L
    coordTable := coordinateTable(k, B);
    membTable := membershipTable(L);
    posTable := positionTable(L);
    --
    coordBits := new MutableHashTable;
    for v in L do (
	c := coordTable#v;
	bits := 0;
	for i from 0 to (k - 1) do (
	    if c#i == 1 then bits = bits + (1 << i);
	    );
	coordBits#v = bits;
	);
    --
    mainSearch := null;
    mainSearch = (i, imgB, usedTable, pivList, mapTable, srcInd) -> (
	if i == k then (
	    if permutationSign(mapTable, srcInd) == 1 then (
		img := for v in L list mapTable#(posTable#v);
		perm := for j from 0 to (n - 1) list mapTable#j;
		return {B, imgB, img, perm};
		);
	    return false;
	    );
	--
	for x in L do (
	    if not usedTable#?x then (
		r := gaussianEliminationBinaryList(cordBits#x, pivList);
		if r != 0 then (
		    col := leadingBit(r);
		    newPivotList := append(pivList, (col, r));
		    imgB2 := append(imgB, x);
		    --
		    result := verifyPartialMap(i, imgB2, L, membTable, coordBits);
		    valid := result#0;
		    newPairs := result#1;
		    --
		    if valid then (
			for p in newPairs do mapTable#(p#0) = p#1;
			newSrcInd := srcInd | (for p in newPairs list p#0);
			--
			usedTable#x = true;
			--
			ans := mainSearch(i+1, imgB2, usedTable, newPivotList, mapTable, newSrcInd);
			--
			remove(usedTable, x);
			for p in newPairs do remove(mapTable, p#0);
			if not isFalse(ans) then return ans;
			);
		    );
		);
	    );
	false
	);
    --
    usedTable0 := new MutableHashTable;
    mapTable0 := new MutableHashTable;
    mainSearch(0, {}, usedTable0, {}, mapTable0, {})
    )



---- NOT FIXED 




-- ============================================================
-- Input validation
-- ============================================================

validateFripBinaryInput = (k,L) -> (
    if k <= 0 then error "validateFripBinaryInput: k must be positive";

    -- Canonical ground-set order for parity computations.
    S := sort(L);
    n := #S;

    -- Simplicity checks: no duplicates, no zero column.
    if #unique(S) != n then error "validateFripBinaryInput: labels must be distinct";
    if any(S, x -> x == 0) then error "validateFripBinaryInput: labels must be nonzero";

    -- Ambient-space sanity: every label must actually lie in GF(2)^k.
    if any(S, x -> x < 0) then error "validateFripBinaryInput: labels must be nonnegative integers";
    if any(S, x -> x >= 2^k) then error "validateFripBinaryInput: some label lies outside GF(2)^k";

    -- Rank check.
    if rankGF2(S,k) != k then error "validateFripBinaryInput: wrong rank for this label list";

    S
);




-- ============================================================
-- Data induced by an ordered image of a basis
-- ============================================================

-- Inputs:
--   S      = sorted ground set
--   coords = coordinate table for a fixed ordered basis B of S
--   Bim    = ordered image of B
--   Sset   = membership table for S
--   pos    = position table for S
--
-- Output:
--   false, if Bim does not define an automorphism of S;
--   otherwise {image, perm}, where
--      image = { T(x) : x in S in sorted order }
--      perm  = { position of T(x) in sorted S : x in S in sorted order }
inducedDataFromBasisImage = (S,coords,Bim,Sset,pos) -> (
    image := {};
    perm := {};

    for x in S do (
        -- For valid input this should never fail: S lies in the span of B.
        if not (coords#?x) then error "inducedDataFromBasisImage: internal error, x missing from coordinate table";

        y := evalMaskGF2(coords#x, Bim);
        image = append(image, y);

        if not (Sset#?y) then return false;

        perm = append(perm, pos#y);
    );

    {image, perm}
);


-- ============================================================
-- Exact search for an odd automorphism
-- ============================================================

-- Returns:
--   false, if there is no odd automorphism;
--   otherwise a witness of the form
--      {B, Bim, image, perm}
--   where:
--      B     = chosen ordered basis of S
--      Bim   = ordered image of B
--      image = images of S in sorted order
--      perm  = induced permutation on positions 0..n-1
oddAutWitnessFripExact = (k,L) -> (
    S := validateFripBinaryInput(k,L);

    B := greedyBasisGF2(S,k);
    coords := coordinateTableGF2(B,k);
    Sset := buildMembershipTable(S);
    pos := buildPositionTable(S);

    -- IMPORTANT:
    -- Declare "search" local first, then assign to it.
    -- This keeps it local to this function and still allows recursion.
    search := null;
    search = (i,Bim,used) -> (
        if i == k then (
            data := inducedDataFromBasisImage(S,coords,Bim,Sset,pos);

            if isFalseBoolean(data) then return false;

            image := data#0;
            perm := data#1;

            if isOddPermutation(perm) then return {B, Bim, image, perm};

            return false;
        );

        -- Try every unused ground-set element as the next image basis vector.
        -- "used" is kept immutable (a list) so backtracking is side-effect free.
        for y in S do (
            if not (member(y,used)) then (
                Bim2 := append(Bim,y);

                if isIndependentGF2(Bim2,k) then (
                    ans := search(i+1, Bim2, append(used,y));
                    if not isFalseBoolean(ans) then return ans;
                );
            );
        );

        false
    );

    search(0, {}, {})
);





hasOddAutFripExact = (k,L) -> (
    W := oddAutWitnessFripExact(k,L);
    not isFalseBoolean(W)

);

withoutOddAutFripExact = (k,L) -> (
    not hasOddAutFripExact(k,L)
);

isFalseBoolean = x -> (
    (class x === Boolean) and (not x)
);

isTrueBoolean = x -> (
    (class x === Boolean) and x
);









