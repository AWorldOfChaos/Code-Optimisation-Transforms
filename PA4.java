import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.TreeMap;

import soot.*;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.jimple.internal.*;
import soot.options.Options;

import javax.swing.text.html.Option;

public class PA4 {
    public static void main(String[] args) {
        String classPath = "."; 	// change to appropriate path to the test class
		String dir = "./testcase/";

        //Set up arguments for Soot
        String[] sootArgs = {
            "-cp", classPath, "-pp",  // sets the class path for Soot
            "-w",                     // whole program analysis
            "-f", "c",                // class file
            "-keep-line-number",      // preserves line numbers in input Java files
            "-main-class", "Test",	  // specify the main class
            "-process-dir", dir,      // directory of classes to analyze
        };

        // Create transformer for analysis
        SceneTransformer analysisTransformer = new AnalysisTransformer();

        // Add transformer to appropriate pack in PackManager; PackManager will run all packs when soot.Main.main is called
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.gc", analysisTransformer));
        PackManager.v().runPacks();
        // Call Soot's main method with arguments
        soot.Main.main(sootArgs);

    }
}
