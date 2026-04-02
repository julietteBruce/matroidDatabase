--------------------------------------------------------------------
--------------------------------------------------------------------
----- These functions are for processing the source data from
----- the raw source data from  located in the Fripertinger-Wild
----- database, located in the "sourceData" folder into a more
----- M2 friendly format stored in the "data" folder.
----- WARNING: Paths are hardcoded 
--------------------------------------------------------------------
--------------------------------------------------------------------

--------------------------------------------------------------------
----- This wrapper loops over all the lines in one of the 6 data
----- subfolder specified by the input string "s"
--------------------------------------------------------------------
convertFile = method();
convertFile (String) := (s) -> (
    inFilesList := lines get ("! ls ../sourceData/" | s);
    print inFilesList;
    apply(inFilesList, F -> (
	    inFile = "../sourceData/" | s |"/"| F;
	    outFile = "data/"|s|"/"|F;
	    print inFile;
	    readDataToLists(inFile,outFile)
	    ))
    )

--------------------------------------------------------------------
----- Reads all of the data in a file -- ignores the first 4 lines,
----- which in Fripertinger-Wild give extra information --
----- and prints the remaining lines to a new file as a M2 list.
--------------------------------------------------------------------
readDataToLists = method();
readDataToLists (String, String) := (inFile, outFile) -> (
    inLines = lines get inFile;
    f := openOut outFile;
    if #inLines > 4 then (
	for i from 4 to (#inLines - 1) do (
	    lineToList := separateRegexp("[ ]", (inLines#i));
	    lineValued := apply(lineToList, i -> value i);
	    f << toExternalString lineValued;
	    f << endl;
	    );
	);
    close(f);
    )


--------------------------------------------------------------------
----- Run this to generate all the data. 
--------------------------------------------------------------------
dataTypes = {"lcBinary","slBinary", "slcBinary", "looplessBinary", "lcRegular"}
dataTypes = {"lcRegular"}
apply(dataTypes, s -> convertFile(s))

