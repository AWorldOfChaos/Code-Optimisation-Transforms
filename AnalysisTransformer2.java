import java.net.Inet4Address;
import java.util.*;

import soot.*;
import soot.JastAddJ.ParameterDeclaration;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.MulExpr;
import soot.jimple.NullConstant;
import soot.jimple.AddExpr;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.EqExpr;
import soot.jimple.ParameterRef;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.util.Chain;
import soot.toolkits.scalar.LiveLocals;


public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        Set<SootMethod> methods = new HashSet<>();
        cg = Scene.v().getCallGraph();
        // Get the main method
        SootMethod mainMethod = Scene.v().getMainMethod();
        // Get the list of methods reachable from the main method
        // Note: This can be done bottom up manner as well. Might be easier to model.

        getlistofMethods(mainMethod, methods);

        for (SootMethod m : methods) {
            processCFG(m);
        }
    }

    private static void getlistofMethods(SootMethod method, Set<SootMethod> reachableMethods) {
        // Avoid revisiting methods
        if (reachableMethods.contains(method)) {
            return;
        }
        // Add the method to the reachable set
        reachableMethods.add(method);

        // Iterate over the edges originating from this method
        Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(method);
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod targetMethod = edge.tgt();
            // Recursively explore callee methods
            if (!targetMethod.isJavaLibraryMethod()) {
                getlistofMethods(targetMethod, reachableMethods);
            }
        }
    }

    protected void processCFG(SootMethod method) {
        if(method.toString().contains("init")  ) { return; }
        Body body = method.getActiveBody();
        // Get the callgraph 
        UnitGraph cfg = new BriefUnitGraph(body);
        // Get live local using Soot's exiting analysis
        LiveLocals liveLocals = new SimpleLiveLocals(cfg);
        // Units for the body
        PatchingChain<Unit> units = body.getUnits();

        // Create a UnitGraph for the body
        UnitGraph unitGraph = new BriefUnitGraph(body);
        
        // Perform simple live locals analysis to determine live variables
        // SimpleLiveLocals liveLocals = new SimpleLiveLocals(unitGraph);
        
        // Create a list to store the dead units
        List<Unit> deadUnits = new ArrayList<>();
        
        for(Unit unit:units) {
            // Check if the unit defines any variables
            if (unit instanceof DefinitionStmt) {
                DefinitionStmt defStmt = (DefinitionStmt) unit;
                Value leftOp = defStmt.getLeftOp();
                
                // Check if the defined variable is not live after this unit
                if (!liveLocals.getLiveLocalsAfter(unit).contains(leftOp)) {
                    // Add the unit to the list of dead units
                    deadUnits.add(unit);
                }
            }
        }
        
        // Remove dead units from the body
        for (Unit deadUnit : deadUnits) {
            // System.out.println(deadUnit.toString());
            body.getUnits().remove(deadUnit);
        }
    }

}
