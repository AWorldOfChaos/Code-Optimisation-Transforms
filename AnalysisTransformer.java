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

        // Iterate through each unit (instruction) in the method body
        Iterator<Unit> unitIterator = body.getUnits().iterator();
        while (unitIterator.hasNext()) {
            Stmt stmt = (Stmt) unitIterator.next();
            // Look for instances of null checks
            if (stmt instanceof IfStmt) {
                IfStmt ifStmt = (IfStmt) stmt;
                Value condition = ifStmt.getCondition();
                if (condition instanceof EqExpr) {
                    EqExpr eqExpr = (EqExpr) condition;
                    Value op1 = eqExpr.getOp1();
                    Value op2 = eqExpr.getOp2();
                    // Check if it's a null check
                    if (op1 instanceof NullConstant || op2 instanceof NullConstant) {
                        // Check if the null check is redundant
                        if (isRedundantNullCheck(body, unitIterator)) {
                            // Remove the null check if it's redundant
                            unitIterator.remove();
                        }
                    }
                }
            }
        }
       
    }

     // Method to check if a null check is redundant
     private boolean isRedundantNullCheck(Body body, Iterator<Unit> unitIterator) {
        // Create a copy of the body's unit list
        List<Unit> units = new ArrayList<>(body.getUnits());

        // Iterate through the units after the null check
        while (unitIterator.hasNext()) {
            Stmt nextStmt = (Stmt) unitIterator.next();
            // If a throw statement is found, the null check is not redundant
            if (nextStmt instanceof ThrowStmt) {
                return false;
            }
        }

        // If no throw statement is found, the null check is redundant
        return true;
    }

}
