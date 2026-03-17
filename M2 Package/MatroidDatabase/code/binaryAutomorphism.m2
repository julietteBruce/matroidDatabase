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
----- DESCRIPTION: Bitwise xor of ingeter vectors, the key
----- is when working with binary vector this is the same as
----- as addition but faster:
----- e.g. 10 + 11 = (1 xOr 1) (0 xOr 1) = 101
--------------------------------------------------------------------
--------------------------------------------------------------------
bitXor = (a,b) -> (
    a ^^ b
);

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
    visited := new MutableList from toList(n : false);
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
    for i in I do (
	if not visited#?i then (
	    cycles = cycles + 1;
	    curPos := i;
	    while not visited#?curPos do (
		visited#curPos = true;
		curPost = P#curPos;
		);
	    );
	);
    (#I - cycles) % 2 
    )

permutationSign({0, 1}) == 0
permutationSign({1,0}) == 1
permutationSign({2, 0, 4, 3, 1}) == 1
permutationSign({0, 2, 4, 3, 1}) == 0

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



gussianEliminationBinaryList (List, List) := (v, pivotList) -> (
    for piv in pivotList do (
	pivotCol := piv#0;
	pivotVec := piv#1;
	if (v >> pivotCol) % 2 == 1 then v = bitXor(v, pivotVec)
	);
    v
    )



isIndependent = (L) -> (
    rankBinaryList(L) == #L
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Uses greedy algorithm to find a subset of a
----- a binary list that is a basis for the span of the list.
--------------------------------------------------------------------
--------------------------------------------------------------------
greedyBinaryBasis = method();
greedyBinaryBasis (List) := (L) -> (
    pivotHash := new MutableHashTable;
    basisList := {};
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
            basisList = append(basisList,v); 
        );
	);
    basisList
    )

greedyBinaryBasis = method();
greedyBinaryBasis (ZZ, List) := (k, L) -> (
    pivotHash := new MutableHashTable;
    basisList := {};
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
            basisList = append(basisList,v); 
        );
	if #basisList == k then return basisList
	);
    )


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



verifyPartialMap = method();
verifyPartialMap (ZZ, List, List, MutableHashTable) :=  (i, B, L, membTable, srcLookUp) -> (
    newPairs := {};
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
	if not membTable#?img then return (false, {});
	--
	dstID := posTable#img;
	srcID := if srcLookup#?src then srcLookup#src
                 else error("no source found for bit pattern " | toString src);
        newPairs = append(newPairs, (srcID, dstID));
	);
    (true, newPairs)
    )


oddAutSearch = method();
oddAutSearch (

hasOddAut = method();
hasOddAut (ZZ, List) := (k, L) -> (
    -- optional validation step, which can be skipped for speed
    if opts.Validate == true then (
	validateBinaryMatroidData(L)
	);
    -- basic set-up
    n := #L;  -- size of ground set
    B := greedyBinaryBasis(k, L); -- basis for span of L
    cordTable := cordinateTable(k, B);
    membTable := membershipTable(L);
    posTable := positionTable(L);
    --
    cordBits := new MutableHashTable;
    for v in L do (
	c := cordTable#v;
	bits := 0;
	for i from 0 to (k - 1) do (
	    if c#i == 1 then bits = bits + (1 << i);
	    );
	cordBits#v = bits;
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
		r := gussianEliminationBinaryList(cordBits#x, pivList);
		if r != 0 then (
		    col := leadingBit(r);
		    newPivotList := append(pivList, (col, r));
		    imgB2 := append(imgB, x)
		    --
		    result := verifyPartialMap(i, imgB2, L, membTable, cordBits);
		    valid := result#0;
		    newPairs := result#1;
		    --
		    if valid then (
			for p in newPairs do mapTable#(p#0) = p#1;
			newSrcInd := srcInd | (for p in newPairs lsit p#0);
			--
			usedTable#x = true;
			--
			ans := mainSearch(i+1, imgB2, usedTable, newPivotList, mapTable, newSrcInd);
			--
			remove(usedTable, x);
			for p in newPairs do remove (mapTable, p#0);
			if not isFalse(ans) then return ans;
			);
		    );
		);
	    );
	false
	);
    --
    usedTable0 = new MutableHashTable;
    mapTable0 = new MutableHashTable;
    mainSearch(0, {}, used0, {}, mapTable0, {})
    
    )



---- NOT FIXED 

-- Coordinate table relative to an ordered basis B.
-- T#x = mask such that x = evalMaskGF2(mask,B).
coordinateTableGF2 = (B,k) -> (
    if #B != k then error "coordinateTableGF2: basis has wrong length";
    if not (isIndependentGF2(B,k)) then error "coordinateTableGF2: B is not independent";

    T := new MutableHashTable;

    for mask from 0 to (2^k - 1) do (
        x := evalMaskGF2(mask,B);

        -- With B a basis, each x in GF(2)^k must occur exactly once.
        if T#?x then error "coordinateTableGF2: duplicate vector found; B is not a basis";

        T#x = mask;
    );

    T
);


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

buildMembershipTable = (S) -> (
    T := new MutableHashTable;
    for x in S do (
        T#x = true;
    );
    T
);

buildPositionTable = (S) -> (
    P := new MutableHashTable;
    for i from 0 to (#S - 1) do (
        P#(S#i) = i;
    );
    P
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









