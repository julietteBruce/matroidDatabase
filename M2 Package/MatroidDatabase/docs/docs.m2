doc ///
   Key 
      MatroidDatabase
   Headline 
      Working with a database of special matroids
   Description
    Text
        Lets look at some matroids! 
///

-*
doc ///
   Key 
    withoutOddAut
    (withoutOddAut,Matroid)
   Headline
    Determines if a matroid admits an odd automorphism
   Usage
    withoutOddAut(M)
   Inputs
    M: Matroid
   Outputs
    : Boolean
   Description
    Text
      Calls getIsos(M,M) from the Matroids package and checks if there are no automorphisms which act as an odd permutation on the ground set. Ground set elements are labeled 
      $\{0,1,2,\dots,n-1\}$ as in the Matroids package. Returns true if no odd automorphisms exist, and false otherwise.
      
      Matroids which admit odd automorphisms vanish in the rational matroid complex. In the 
      example below, we ask whether the uniform matroids $U_{2,4}$ admits odd automorphisms. 
      That is, a matroid automorphism given by an odd permutation of its ground set $\{0,1,2,3\}.$
    Example
      M = uniformMatroid(2,4);
      withoutOddAut(M)

///*-
