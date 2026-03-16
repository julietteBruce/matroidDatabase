needsPackage "Matroids";
needsPackage "SpechtModule";

--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: (n) = a positive integer
-----
----- OUPUT: a number
-----
----- DESCRIPTION: Returns the number of digits of n written in
----- binary, i.e., smallest i such that 2^i >= n.
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
fileList = lines get "! ls simpleRegularLooplessMatroids";
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
    "simpleRegularLooplessMatroids/reg_simple_con"|toString(L#0)|"_"|toString(L#1)|".txt"
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
    	return apply(L1,i->convertListToMatroid(i) );
	)
    else return "No data for this {N,K}."
    )

--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: (L) = a list 
-----
----- OUPUT: A list of matroids
-----
----- DESCRIPTION: Given a list L={N,K} this function returns a list
----- of all the regular, simple, connected matroids 
----- whose base set has size N with rank K,  up to isomorphism. 
----- This is done by loading the matroids from the corresponding 
----- data file generated from the Fripertinger-Wild data - in the 
----- simpleRegularLooplessMatroids folder. 
-----
--------------------------------------------------------------------
--------------------------------------------------------------------

rslcMatroidsAsMatrices = method();
rslcMatroidsAsMatrices (List) := (L) ->(
    if noMatroidsNK(L) then return {};
    if member(L,dataRange) then (
	L1 := value get dataFileNameFromList(L);
    	return apply(L1,i->convertListToMatrix(i) );
	)
    else return "No data for this {N,K}."
    )


--------------------------------------------------------------------
--------------------------------------------------------------------
----- INPUT: () = a positive integer
-----
----- OUPUT: A list of matroids
-----
----- DESCRIPTION: Given a positive integer N, returns all regular, 
----- simple connected matroids on [N]. 
-----
--------------------------------------------------------------------
--------------------------------------------------------------------

rslcMatroidsOnN = method();
rslcMatroidsOnN (ZZ) := (N) -> (
    if N<=0 then return "N is not positive";
    if N>=16 then return "no data";
    return flatten for K in (1..N) list rslcMatroids({N,K});
    )


	    ))))
	    return apply(L1,i->withoutOddAutFrip(r,i))
	)
	))

   
