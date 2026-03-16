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


-- ============================================================
-- Basic assertion helper
-- ============================================================

assertTrue = (cond, msg) -> (
    if not cond then error msg;
    true
);


-- ============================================================
-- Low-level GF(2) bit-vector utilities
-- ============================================================

-- Bitwise XOR on integer-encoded vectors.
bitXorGF2 = (a,b) -> (
    a ^^ b
);

-- Position of the highest nonzero bit of x.
-- Example: leadBitGF2(1)=0, leadBitGF2(24)=4.
leadBitGF2 = x -> (
    if x == 0 then error "leadBitGF2 called on 0";

    j := -1;
    y := x;
    while y > 0 do (
        y = y >> 1;
        j = j + 1;
    );
    j
);

-- Rank over GF(2) of a list of vectors in GF(2)^k.
-- ASSUMPTION: every element of L lies in {0,...,2^k-1}.
rankGF2 = (L,k) -> (
    pivots := new MutableHashTable;
    r := 0;

    for x0 in L do (
        x := x0;

        -- Eliminate using existing pivots from high bit to low bit.
        for j in reverse(toList(0..(k-1))) do (
            if (pivots#?j) and ((((x >> j) & 1) == 1)) then (
                x = bitXorGF2(x, pivots#j);
            );
        );

        -- If something remains, it becomes a new pivot.
        if x != 0 then (
            pivotIndex := leadBitGF2(x);
            pivots#pivotIndex = x;
            r = r + 1;
        );
    );

    r
);

isIndependentGF2 = (L,k) -> (
    rankGF2(L,k) == #L
);

-- Greedily extract a basis from a spanning set S.
greedyBasisGF2 = (S,k) -> (
    B := {};

    for x in S do (
        if isIndependentGF2(append(B,x),k) then (
            B = append(B,x);
        );
        if #B == k then return B;
    );

    error "greedyBasisGF2: S does not have rank k"
);

-- Evaluate the mask "mask" against the ordered basis B.
-- If mask = sum_i m_i 2^i, return sum_i m_i B_i in GF(2)^k.
evalMaskGF2 = (mask,B) -> (
    x := 0;

    for i from 0 to (#B - 1) do (
        if (((mask >> i) & 1) == 1) then (
            x = bitXorGF2(x, B#i);
        );
    );

    x
);

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

isOddPermutation = p -> (
    t := 0;

    for i from 0 to (#p - 1) do (
        for j from (i + 1) to (#p - 1) do (
            if p#i > p#j then (
                t = 1 - t;
            );
        );
    );

    t == 1
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









