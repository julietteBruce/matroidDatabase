-- -*- coding: utf-8 -*-
--------------------------------------------------------------------------------
-- Copyright 2025  Juliette Bruce, Maya Banks, John Cobb
--
-- This program is free software: you can redistribute it and/or modify it under
-- the terms of the GNU General Public License as published by the Free Software
-- Foundation, either version 3 of the License, or (at your option) any later
-- version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
-- details.
--
-- You should have received a copy of the GNU General Public License along with
-- this program.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- PURPOSE : A package for working with a database of special matroids
--
--
-- PROGRAMMERS : Madeline Brandt, Juliette Bruce, Daniel Corey
--
--
-- UPDATE HISTORY #0 - 2021 Project Began 
--
--
-- UPDATE HISTORY #1 - March 2026: GitReposity Created
--
--
-- UPDATE HISTORY #2 - 
--
--
-- TO DO LIST : create tests, create docs
--------------------------------------------------------------------------------



newPackage("MatroidDatabase",
    Version => "0.0",
    Date => "16 March 2026",
    Headline => "Working with a database of special matroids",
    Authors => {
	        {
            Name => "Madeline Brandt",
            Email =>"",
	    HomePage => ""
        },
        {
            Name => "Juliette Bruce",
            Email => "juliette.bruce@dartmouth.edu",
            HomePage => "https://www.juliettebruce.xyz"
        },
        {
            Name => "Daniel Corey",
            Email => "",
	    HomePage => ""
        }},
  PackageExports => {"Matroids"},
  DebuggingMode => true,
  AuxiliaryFiles => true,
  Reload => true
  )

export {

  }

--------------------------------------------------------------------
--------------------------------------------------------------------
----- CODE
--------------------------------------------------------------------
--------------------------------------------------------------------
load "MatroidDatabase/code/core.m2"
load "MatroidDatabase/code/binaryAutomorphisms.m2"


--------------------------------------------------------------------
--------------------------------------------------------------------
----- TESTS
--------------------------------------------------------------------
--------------------------------------------------------------------
load "MatroidDatabase/tests/tests.m2"


--------------------------------------------------------------------
--------------------------------------------------------------------
----- DOCUMENTATION
--------------------------------------------------------------------
--------------------------------------------------------------------
beginDocumentation ()    
load "MatroidDatabase/docs/docs.m2"

--------------
end


--------------------------------------------------------------------
--------------------------------------------------------------------
----- Beginning of sandbox
--------------------------------------------------------------------
--------------------------------------------------------------------

---
---
restart
uninstallPackage "MatroidDatabase"
restart
debug needsPackage "MatroidDatabase"
check "MatroidDatabase"
installPackage "MatroidDatabase"
