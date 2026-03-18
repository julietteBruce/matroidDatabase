needsPackage "Matroids";

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

permutationSign (MutableHashTable, List) := (P, I) -> (   
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

isOdd = method();
isOdd (List) := (L) -> (
    permutationSign(L) == 1
    )


isEven = method();
isEven (List) := (L) -> (
    permutationSign(L) == 0
    )


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

--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: Does Guassian elimination on a binary list
----- using bit operations without making matrix
--------------------------------------------------------------------
--------------------------------------------------------------------
gaussianEliminationBinaryList = method();
gaussianEliminationBinaryList (List) := (L) -> (
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

gaussianEliminationBinaryList (ZZ, List) := (v, pivotList) -> (
    for piv in pivotList do (
	pivotCol := piv#0;
	pivotVec := piv#1;
	if (v >> pivotCol) % 2 == 1 then v = bitXor(v, pivotVec)
	);
    v
    )

isIndependent = (L) -> (
    (gaussianEliminationBinaryList(L))#0 == #L
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
--------------------------------------------------------------------
----- DESCRIPTION: Given a vector v in (Z/2Z)^k and a binary list
----- B this essentally does B*v without matrices:
----- v = sum v_i 2^i and B = {b1, b2, ..., bt} then 
----- output is sum v_i*b_i
---------------------------------------------------------------------
---------------------------------------------------------------------
multiplyBinaryList = method();
multiplyBinaryList (ZZ, List) := (v, B) -> (
    n := 0;
    for i from 0 to (#B - 1) do (
	if (((v >> i) & 1) == 1) then (n = bitXor(n, B#i));
	);
    n
    )


-*-- FIX 3 & 4: Changed parameter names for clarity;
-- 3rd argument must be posTable (vector -> position index), not membTable
-- 4th argument must be coordToPos (bitmask -> position index), not coordBits
verifyPartialMap = method();
verifyPartialMap (ZZ, List, MutableHashTable, MutableHashTable) :=  (i, B, posTable, coordToPos) -> (
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
	srcID := if coordToPos#?src then coordToPos#src
                 else error("no source found for bit pattern " | toString src);
        newPairs#(#newPairs) = (srcID, dstID);
	);
    (true, toList newPairs)
    )*-

verifyPartialMap = method();

-- stageData is a list of pairs (srcMask, srcID), where
--   srcMask = coordinate bitmask of an actual source element v in L
--   srcID   = its position in L
verifyPartialMap (List, List, MutableHashTable) := (imgB, stageData, posTable) -> (
    newPairs := new MutableList from {};
    for p in stageData do (
        srcMask := p#0;
        srcID   := p#1;
        img := multiplyBinaryList(srcMask, imgB);
        if not posTable#?img then return (false, {});
        newPairs#(#newPairs) = (srcID, posTable#img);
    );
    (true, toList newPairs)
);

membershipTable = method();
membershipTable (List) := (L) -> (
    membTable := new MutableHashTable;
    for x in L do membTable#x = true;
    membTable
    )

--ONLY WORKS FOR NON-DUPLICATES, FINE BECAUSE SIMPLE
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
    if not (isIndependent(B)) then error "B is not independent";
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
)

isFalse = x -> (
    (class x === Boolean) and (not x)
)


oddAutSearch = method(Options => {Validate => false});
oddAutSearch (ZZ, List) := opts -> (k, L) -> (
    n := #L;
    B := greedyBinaryBasis(k, L);
    coordTable := coordinateTable(k, B);
    posTable := positionTable(L);

    coordBits := new MutableHashTable;
    for v in L do coordBits#v = coordTable#v;

    -- actual source elements, grouped by highest nonzero coordinate bit
    sourceByLead := new MutableHashTable;
    for i from 0 to k-1 do sourceByLead#i = new MutableList from {};

    for v in L do (
        c := coordBits#v;
        j := leadingBit(c);
        M := sourceByLead#j;
        M#(#M) = (c, posTable#v);
    );

    mainSearch := null;
    mainSearch = (i, imgB, usedTable, pivList, mapTable) -> (
        if i == k then (
            perm := for j from 0 to (n - 1) list mapTable#j;
            if permutationSign(perm) == 1 then (
                img := for j from 0 to (n - 1) list L#(perm#j);
                return {B, imgB, img, perm};
            );
            return false;
        );

        for x in L do (
            if not usedTable#?x then (
                r := gaussianEliminationBinaryList(coordBits#x, pivList);
                if r != 0 then (
                    col := leadingBit(r);
                    newPivotList := append(pivList, (col, r));
                    imgB2 := append(imgB, x);

                    result := verifyPartialMap(imgB2, toList(sourceByLead#i), posTable);
                    valid := result#0;
                    newPairs := result#1;

                    if valid then (
                        for p in newPairs do mapTable#(p#0) = p#1;
                        usedTable#x = true;

                        ans := mainSearch(i+1, imgB2, usedTable, newPivotList, mapTable);

                        remove(usedTable, x);
                        for p in newPairs do remove(mapTable, p#0);

                        if not isFalse(ans) then return ans;
                    );
                );
            );
        );
        false
    );

    usedTable0 := new MutableHashTable;
    mapTable0 := new MutableHashTable;
    mainSearch(0, {}, usedTable0, {}, mapTable0)
)

hasOddAutFripExact = (k,L) -> (
    W := oddAutSearch(k,L);
    not isFalse(W)
)


--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: (L) = a list representing a matroid
-----
----- OUPUT: A matrix representing the matroid
-----
----- DESCRIPTION: Given a list L = {L1,L2,...,Ln} of positive intgers
----- which represents a matroid in Fripertinger-Wild form, this
----- returns the matrix M whose i-th column is the base 2 expansion
----- of Li written increasingly and padded with zeros so every 
----- element of L has a base 2 expansion of the same length. The
----- resulting matrix M represents the matroid over ZZ/2.
-----
--------------------------------------------------------------------
--------------------------------------------------------------------

binaryColumnsMatrix = method();
binaryColumnsMatrix (List) := (L) ->(
    if any(L, i -> (not instance(i,ZZ)) or i < 0) then error "expected list of positive integers.";
    --
    if L == {} then return sub(matrix {}, GF(2));
    --
    maxLength := max apply(L, l -> bitLength(l));
    --
    matList := apply(maxLength, r -> apply(L, i -> (i // 2^r) % 2));
    sub(matrix matList, ZZ/2)
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: (M) = a matrix representing a matroid
-----
----- OUPUT: A list representing the matroid
-----
----- DESCRIPTION: Given a binary matrix M with columns (M1,M2,...Mn) 
----- representing a matroid over ZZ/2 this returns a list of positive
----- integers L = {L1,L2,...,Ln} such that the i-th  column is the
----- base 2 expansion of Li written increasingly and padded with 
----- zeros so every element of L has a base 2 expansion of the same 
----- length. The list L is the Fripertinger-Wild representation of
----- of the matroid represented by M.
-----
--------------------------------------------------------------------
--------------------------------------------------------------------

binaryMatrixToList = method();
binaryMatrixToList(Matrix) := M -> (
    if (ring M) =!= ZZ/2 then error "expect matrix to be defined over ZZ/2.";
    cols := entries transpose M;
    apply(cols, v -> sum(#v, j -> if v#j == 0 then 0 else 2^j))
    )



--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: (L) = a list representing a matroid
-----
----- OUPUT: A matroid
-----
----- DESCRIPTION: Given a list L = {L1,L2,...,Ln} of positive intgers
----- which represents a matroid in Fripertinger-Wild form, this
----- returns matroid corresponding to the matrix from the function 
----- "binaryColumnsMatrix" 
-----
--------------------------------------------------------------------
--------------------------------------------------------------------

fwListToMatroid = method();
fwListToMatroid (List) := (L) -> matroid(binaryColumnsMatrix(L))




--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: This snippet of code goes through all of the files
----- in the simpleRegularLooplessMatroids folder, and extracts the 
----- size of the base set and the rank for each given file. For
----- example, reg_simple_con3_2.txt is converted to the list {3,2}.
----- The output is a list of these pairs called dataRange.
--------------------------------------------------------------------
--------------------------------------------------------------------
fileList = lines get "! ls slcRegular";
dataRange = apply(fileList,s->(
	S := separateRegexp("[_]",s);
	L := separateRegexp("[.]",S#3);
	{value substring(3,(S#2)),value L#0}
	));



--------------------------------------------------------------------
--------------------------------------------------------------------
----- DESCRIPTION: This is a list of pairs {N,K} for K<=N-1 where we 
----- know that there are no simple, connected, regular matroids on 
----- [N] of rank K. There are no such matroids when K>=N.
--------------------------------------------------------------------
--------------------------------------------------------------------
dataZero = {{2,1},{3,1},{4,1},{4,2},{5,1},{5,2},{6,1},{6,2},{7,1},{7,2},
    {7,3},{8,1},{8,2},{8,3},{9,1},{9,2},{9,3},{10,1},{10,2},{10,3},{11,1},
    {11,2},{11,3},{11,4},{12,1},{12,2},{12,3},{12,4},{13,1},{13,2},{13,3},
    {13,4},{14,1},{14,2},{14,3},{14,4},{15,1},{15,2},{15,3},{15,4}};



--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: (L) = a list
-----
----- OUPUT: true or false
-----
----- DESCRIPTION: Given a list L={N,K} of two numbers N and K 
----- representing size of the base set and rank of the matroid
----- this returns true if there are no regular, simple, connected 
----- rank K matroids on [N]. 
-----
--------------------------------------------------------------------
--------------------------------------------------------------------

noMatroidsNK = method();
noMatroidsNK (List) := (L) ->(
    N:=L#0; K:=L#1; 
    if (N>=2 and K>=N) then return true;
    if (N==1 and K>N) then return true;
    if member(L,dataZero) then return true;
    if not member(L,dataRange) then return "no data for this {N,K}";
    return false
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: (L) = a list
-----
----- OUPUT: A string representing a file name
-----
----- DESCRIPTION: Given a list L={N,K} of two numbers N and K 
----- representing size of the base set  and rank of the matroid
----- this returns the file name and path for the corresponding 
----- file in the simpleRegularLooplessMatroids folder as a string. 
----- Specifically it returns
----- "simpleRegularLooplessMatroids/reg_simple_conN_K" 
----- where N and K have been converted to strings. 
-----
--------------------------------------------------------------------
--------------------------------------------------------------------

dataFileNameFromList = method();
dataFileNameFromList (List) := (L) ->(
    "slcRegular/reg_simple_con"|toString(L#0)|"_"|toString(L#1)|".txt"
    )



--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: (L) = a list 
-----
----- OUPUT: A list of matrices
-----
----- DESCRIPTION: Given a list L={N,K} this function returns a list
----- of all the regular, simple, connected matroids 
----- whose base set has size N with rank K,  up to isomorphism
----- represented as N (columns) x K (rows) matrices.
----- This is done by loading the matroids from the corresponding 
----- data file generated from the Fripertinger-Wild data - in the 
----- simpleRegularLooplessMatroids folder. 
-----
--------------------------------------------------------------------
--------------------------------------------------------------------

rslcMatroids = method();
rslcMatroids (List) := (L) ->(
    if noMatroidsNK(L) then return {};
    if member(L,dataRange) then (
	L1 := value get dataFileNameFromList(L);
    	return apply(L1,i->fwListToMatroid(i) );
	)
    else return "No data for this {N,K}."
    )






createBasisFile = method();
createBasisFile (ZZ, ZZ) := (n, r) -> (
    basisList := rankedBasis(n,r);
    fileName := "comp/slcRegular/slcRegular_"|toString(n)|"_"|toString(r)|".txt";
    f := openOut fileName;
    for M in basisList do (
	B := bases(M);
	E := toList groundSet(M);
	f << toExternalString {E, B};
	f << endl;
	);
    close(f)
    )


time apply(toList(1..15), n ->(apply(toList(0..n), r -> (
		if member({n,r}, dataRange) then (
		    print (n,r);
		    L1 := value get dataFileNameFromList({n,r});
		    time basisList := delete(,apply(L1, l -> (
			    if hasOddAutFripExact(r,l) == false then fwListToMatroid(l)
			    )));
		    fileName := "comp/slcRegular/slcRegular_"|toString(n)|"_"|toString(r)|".txt";
		    f := openOut fileName;
		    for M in basisList do (
			B := bases(M);
			E := toList groundSet(M);
			f << toExternalString {E, B};
			f << endl;
			);
		    close(f)
		    )
		else (
		    fileName := "comp/slcRegular/slcRegular_"|toString(n)|"_"|toString(r)|".txt";
		    f := openOut fileName;
		    close(f)
		    );
		))))
	    
	    ))
    )

readBasisFile = method();
readBasisFile (ZZ, ZZ, String) := (n, r, s) -> (
    fileName := "comp/slcRegular/slcRegular_"|toString(n)|"_"|toString(r)|".txt";
    fileLines := lines get fileName;
    apply(fileLines, l -> (
	    L := value l;
	    E := L#0;
	    B := L#1;
	    matroid(E,B)
	    ))
    )

slcReg = apply(toList(1..15), n->apply(toList(0..n), r->(try readBasisFile(n,r,"slcRegular") else infinity)))
apply(slcReg,n->apply(n,r->(
	    if not instance(r,List) then infinity
	    else #r)))

--------------------------------------------------------------------
--------------------------------------------------------------------



hasOddAutOLD = method();
hasOddAutOLD(Matroid) := (M) -> (
    any(getIsos(M,M), perm -> permutationSign(perm) == 1)
)


L1 = value get dataFileNameFromList({10,5});
apply(L1, l ->(
	M := fwListToMatroid(l);
	hasOddAutOLD(M)
	))
apply(L1, l->hasOddAutFripExact(5,l))


time apply(toList(1..11), n ->(apply(toList(0..n), r -> (
		if member({n,r}, dataRange) then (
		    apply(L1, l ->(hasOddAutFripExact(r,l)));
			)
		    ))
		))
      

time apply(toList(1..11), n ->(apply(toList(0..n), r -> (
		if member({n,r}, dataRange) then (
		    print (n,r);
		    L1 := value get dataFileNameFromList({n,r});
		    time apply(L1, l -> (
			    M :=  fwListToMatroid(l);
			    hasOddAutOLD(M);
			    ))
		    ))
	    ))
    )


time apply(toList(1..11), n ->(apply(toList(0..n), r -> (
		if member({n,r}, dataRange) then (
		    print (n,r);
		    L1 := value get dataFileNameFromList({n,r});
		    time apply(L1, l -> (
			    hasOddAutFripExact(r,l);
			    ))
		    ))
	    ))
    )













