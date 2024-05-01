import java.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.AnyNewExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.*;
import soot.jimple.internal.JNewExpr;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.HashMap;
import java.util.Map;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Set;
import java.util.Collections;


public class AnalysisTransformer extends BodyTransformer {  
    public static ArrayList<String> resultList = new ArrayList<>();
    
    @Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
        // Construct CFG for the current method's body
        PatchingChain<Unit> units = body.getUnits();

        SootClass declaringClass = body.getMethod().getDeclaringClass();
        String className = declaringClass.getName();
        String methodName = body.getMethod().getName();

        Map<String, Set<Integer>> stackMap = new HashMap<>();
        Map<AbstractMap.SimpleEntry<Integer, String>, Set<Integer>> HeapMap = new HashMap<>();
        Set<Integer> escaped = new HashSet<>();
        ArrayList<String> params = new ArrayList<>();
        ArrayList<Integer> param_escapers = new ArrayList<>();
        ArrayList<Integer> func_escapers = new ArrayList<>();
        
        for (Unit u : units) {
            if (u instanceof JAssignStmt) {
                JAssignStmt stmt = (JAssignStmt) u;
                Value rhs = stmt.getRightOp();
                if (rhs instanceof JNewExpr) {
                    try {
                        int lineNumber = u.getJavaSourceStartLineNumber();

                        // Assuming you want to use the rhs as a key in stackMap
                        String key = stmt.getLeftOp().toString(); 

                        // Add (rhs, lineNumber) to stackMap
                        Set<Integer> temp = new HashSet<>();
                        temp.add(lineNumber);
                        stackMap.put(key, temp);

                    } catch (Exception e) {
                        System.out.println("Unit is " + u + " and the line number is : " + -1);
                    }
                }
                else if (stmt.containsArrayRef()) {
                    // System.out.println("Array Element Assignment" + stmt);
                } else if (stmt.getRightOp() instanceof FieldRef) {

                    if (stmt.getRightOp() instanceof InstanceFieldRef){
                        InstanceFieldRef fieldRef = (InstanceFieldRef) stmt.getRightOp();

                        // Extract components
                        String sourceVariable = fieldRef.getBase().toString();
                        String fieldName = fieldRef.getField().getName();
                        
                        String ref = stmt.getLeftOp().toString();
                        Set<Integer> obj;
                        
                        if (stackMap.get(sourceVariable)!=null){
                            obj = new HashSet<>();
                            for (int element : stackMap.get(sourceVariable)){
                                if (HeapMap.get(new AbstractMap.SimpleEntry<>(element, fieldName)) != null)
                                obj.addAll(HeapMap.get(new AbstractMap.SimpleEntry<>(element, fieldName)));
                                else
                                obj.add(-1);
                            }
                        }
                        else{
                            obj = new HashSet<>();
                            obj.add(-1);
                        }

                        if (params.contains(ref)){
                            for(int element : obj){
                                param_escapers.add(element);
                            }
                        }
                        stackMap.put(ref, obj);
                    }
                    else if (stmt.getRightOp() instanceof StaticFieldRef){
                        StaticFieldRef fieldRef = (StaticFieldRef) stmt.getRightOp();

                        // Extract components
                        String sourceVariable = fieldRef.getField().getName();

                        String ref = stmt.getLeftOp().toString();
                        Set<Integer> obj;
                        
                        if (stackMap.get(sourceVariable)!=null){
                            obj = new HashSet<>();
                            for (int element : stackMap.get(sourceVariable)){
                                if (HeapMap.get(new AbstractMap.SimpleEntry<>(element, sourceVariable)) != null)
                                obj.addAll(HeapMap.get(new AbstractMap.SimpleEntry<>(element, sourceVariable)));
                                else
                                obj.add(-1);
                            }
                            obj = HeapMap.get(new AbstractMap.SimpleEntry<>(stackMap.get(sourceVariable), sourceVariable));
                        }
                        else{
                            obj = new HashSet<>();
                            obj.add(-1);
                        }

                        if (params.contains(ref)){
                            for(int element : obj){
                                param_escapers.add(element);
                            }
                        }
                        stackMap.put(ref, obj);

                    }

                } else if (stmt.getLeftOp() instanceof FieldRef) {

                    if (stmt.getLeftOp() instanceof InstanceFieldRef){
                        InstanceFieldRef fieldRef = (InstanceFieldRef) stmt.getLeftOp();

                        // Extract components
                        String targetVariable = fieldRef.getBase().toString();
                        String fieldName = fieldRef.getField().getName();

                        String ref = stmt.getRightOp().toString();
                        Set<Integer> obj = new HashSet<>();
                        if(stackMap.get(ref) != null){
                            for(int element : stackMap.get(ref)){
                                obj.add(element);
                            }
                        }

                        if (params.contains(targetVariable)){
                            for (int element : obj){
                                param_escapers.add(element);
                            }
                        }
                        else{
                            if (stackMap.get(targetVariable)!= null){
                                for (int element : stackMap.get(targetVariable)){
                                    Set<Integer> temp = new HashSet<>();
                                    temp.addAll(obj);
                                    if (HeapMap.get(new AbstractMap.SimpleEntry<>(element, fieldName)) == null){
                                        HeapMap.put(new AbstractMap.SimpleEntry<>(element, fieldName), temp);
                                    }
                                    else{
                                        temp.addAll(HeapMap.get(new AbstractMap.SimpleEntry<>(element, fieldName)));
                                        HeapMap.put(new AbstractMap.SimpleEntry<>(element, fieldName), temp);
                                    } 
                                }
                            }
                            else
                            HeapMap.put(new AbstractMap.SimpleEntry<>(-1, fieldName), obj);
                        }

                    }
                    else if (stmt.getLeftOp() instanceof StaticFieldRef){
                        StaticFieldRef fieldRef = (StaticFieldRef) stmt.getLeftOp();

                        // Extract components
                        String targetVariable = fieldRef.getField().getName();

                        String ref = stmt.getRightOp().toString();
                        Set<Integer> obj = new HashSet<>();
                        for(int element : stackMap.get(ref)){
                            obj.add(element);
                        }

                        if (params.contains(targetVariable)){
                            for (int element : obj){
                                param_escapers.add(element);
                            }
                        }
                        else{
                            if (stackMap.get(targetVariable)!= null){
                                for (int element : stackMap.get(targetVariable)){
                                    Set<Integer> temp = new HashSet<>();
                                    temp.addAll(obj);
                                    if (HeapMap.get(new AbstractMap.SimpleEntry<>(element, targetVariable)) == null){
                                        HeapMap.put(new AbstractMap.SimpleEntry<>(element, targetVariable), temp);
                                    }
                                    else{
                                        temp.addAll(HeapMap.get(new AbstractMap.SimpleEntry<>(element, targetVariable)));
                                        HeapMap.put(new AbstractMap.SimpleEntry<>(element, targetVariable), temp);
                                    } 
                                }
                            }
                            else
                            HeapMap.put(new AbstractMap.SimpleEntry<>(-1, targetVariable), obj);
                        }
                    }
                }
                else if (rhs instanceof JStaticInvokeExpr){
                    JStaticInvokeExpr staticInvokeExpr = (JStaticInvokeExpr) rhs;

                    // Extract the method signature
                    String methodSignature = staticInvokeExpr.getMethodRef().getSignature();

                    // Extract the arguments
                    int argCount = staticInvokeExpr.getArgCount();
                    for (int i = 0; i < argCount; i++) {
                        Value argValue = staticInvokeExpr.getArg(i);

                        Set<Integer> startEntry = new HashSet<>();
                        if (stackMap.get(argValue.toString()) != null){
                        startEntry.addAll(stackMap.get(argValue.toString()));
                        }

                        for(int element : startEntry){
                            func_escapers.add(element);
                        }
                    }
                }
                else if (rhs instanceof JVirtualInvokeExpr){
                    JVirtualInvokeExpr staticInvokeExpr = (JVirtualInvokeExpr) rhs;

                    // Extract the method signature
                    String methodSignature = staticInvokeExpr.getMethodRef().getSignature();

                    // Extract the arguments
                    int argCount = staticInvokeExpr.getArgCount();
                    for (int i = 0; i < argCount; i++) {
                        Value argValue = staticInvokeExpr.getArg(i);

                        Set<Integer> startEntry = new HashSet<>();
                        if (stackMap.get(argValue.toString()) != null){
                        startEntry.addAll(stackMap.get(argValue.toString()));
                        }

                        for(int element : startEntry){
                            func_escapers.add(element);
                        }
                    }
                    Value baseValue = staticInvokeExpr.getBase();
                    Set<Integer> startEntry = new HashSet<>();
                    if (stackMap.get(baseValue.toString()) != null){
                    startEntry.addAll(stackMap.get(baseValue.toString()));
                    }

                    for(int element : startEntry){
                        func_escapers.add(element);
                    }
                }
            }
            else if (u instanceof JReturnStmt){
                JReturnStmt returnStmt = (JReturnStmt) u;
                Set<Integer> startEntry = new HashSet<>();
                startEntry = stackMap.get(returnStmt.getOp().toString());

                if (startEntry != null){
                    for(int element : startEntry){
                        // Set to store visited integers
                        Set<Integer> visitedIntegers = new HashSet<>();

                        // Perform the traversal
                        try{
                        traverseHeapMap(HeapMap, element, visitedIntegers);
                        }
                        catch (Exception e) {
                            System.out.println(e);
                        }

                        // Print the visited integers
                        escaped.addAll(visitedIntegers);
                    }
                }
            }
            else if (u instanceof JReturnVoidStmt){
                // System.out.println("wow");
            }
            else if (u instanceof JInvokeStmt){
                JInvokeStmt invokeStmt = (JInvokeStmt) u;
                InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();

                if (invokeExpr instanceof StaticInvokeExpr) {
                    StaticInvokeExpr staticInvokeExpr = (StaticInvokeExpr) invokeExpr;

                    // Extract the method signature
                    String methodSignature = staticInvokeExpr.getMethodRef().getSignature();

                    // Extract the arguments
                    int argCount = staticInvokeExpr.getArgCount();
                    for (int i = 0; i < argCount; i++) {
                        Value argValue = staticInvokeExpr.getArg(i);

                        Set<Integer> startEntry = new HashSet<>();
                        if (stackMap.get(argValue.toString()) != null){
                            startEntry.addAll(stackMap.get(argValue.toString()));
                        }
                        
                        for(int element : startEntry){
                            func_escapers.add(element);
                        }
                    }
                }
                else if (invokeExpr instanceof VirtualInvokeExpr){
                    VirtualInvokeExpr staticInvokeExpr = (VirtualInvokeExpr) invokeExpr;

                    // Extract the method signature
                    String methodSignature = staticInvokeExpr.getMethodRef().getSignature();

                    // Extract the arguments
                    int argCount = staticInvokeExpr.getArgCount();
                    for (int i = 0; i < argCount; i++) {
                        Value argValue = staticInvokeExpr.getArg(i);

                        Set<Integer> startEntry = new HashSet<>();
                        
                        if (stackMap.get(argValue.toString()) == null)
                        startEntry.add(-1);
                        else
                        startEntry = stackMap.get(argValue.toString());

                        for(int element : startEntry){
                            // Set to store visited integers
                            Set<Integer> visitedIntegers = new HashSet<>();

                            // Perform the traversal
                            try{
                            traverseHeapMap(HeapMap, element, visitedIntegers);
                            }
                            catch (Exception e) {
                                System.out.println(e);
                            }

                            escaped.addAll(visitedIntegers);
                        }

                    }

                    Value argValue = staticInvokeExpr.getBase();

                    Set<Integer> startEntry = new HashSet<>();
                    
                    if (stackMap.get(argValue.toString()) == null)
                    startEntry.add(-1);
                    else
                    startEntry = stackMap.get(argValue.toString());

                    for(int element : startEntry){
                        // Set to store visited integers
                        Set<Integer> visitedIntegers = new HashSet<>();

                        // Perform the traversal
                        try{
                        traverseHeapMap(HeapMap, element, visitedIntegers);
                        }
                        catch (Exception e) {
                            System.out.println(e);
                        }

                        escaped.addAll(visitedIntegers);
                    }
                }
            }
            else if (u instanceof JIdentityStmt)
            {
                JIdentityStmt identityStmt = (JIdentityStmt) u;

                // Extract the left-hand side (LHS) operand
                String param = identityStmt.getLeftOp().toString();
                params.add(param);
            }
        }

        if (true)
        {
            int startEntry = -1;
            Set<Integer> visitedIntegers = new HashSet<>();
            // Perform the traversal
            try{
            traverseHeapMap(HeapMap, startEntry, visitedIntegers);
            }
            catch (Exception e) {
                System.out.println(e);
            }
            escaped.addAll(visitedIntegers);
        }
        for (int startEntry : func_escapers){
            Set<Integer> visitedIntegers = new HashSet<>();
            // Perform the traversal
            try{
            traverseHeapMap(HeapMap, startEntry, visitedIntegers);
            }
            catch (Exception e) {
                System.out.println(e);
            }

            escaped.addAll(visitedIntegers);
        }
        
        for (int startEntry : param_escapers){
            Set<Integer> visitedIntegers = new HashSet<>();
            // Perform the traversal
            try{
            traverseHeapMap(HeapMap, startEntry, visitedIntegers);
            }
            catch (Exception e) {
                System.out.println(e);
            }
            escaped.addAll(visitedIntegers);
        }
        escaped.remove(-1);

        String result = buildResultString(className, methodName, escaped);
        if (!escaped.isEmpty()) resultList.add(result);
    }

    private static void traverseHeapMap(Map<AbstractMap.SimpleEntry<Integer, String>, Set<Integer>> heapMap,
                                        int currentInteger,
                                        Set<Integer> visitedIntegers) {
        // Check if the current integer has not been visited
        if (!visitedIntegers.contains(currentInteger)) {
            // Mark the current integer as visited
            visitedIntegers.add(currentInteger);

            // Print information or perform any other desired action

            // Traverse all entries associated with the current integer
            for (Map.Entry<AbstractMap.SimpleEntry<Integer, String>, Set<Integer>> entry : heapMap.entrySet()) {
                if (entry.getKey().getKey().equals(currentInteger)) {
                    for (int element : entry.getValue())
                    traverseHeapMap(heapMap, element, visitedIntegers);
                }
            }
        }
    }

    private static String buildResultString(String className, String methodName, Set<Integer> escaped) {
        // Create a StringBuilder to build the result string
        StringBuilder resultBuilder = new StringBuilder();

        // Append className and methodName to the result string
        resultBuilder.append(className).append(":").append(methodName).append(" ");

        // Sort the elements of the escaped set
        ArrayList<Integer> sortedEscaped = new ArrayList<>(escaped);
        Collections.sort(sortedEscaped);

        // Append sorted elements to the result string
        for (int element : sortedEscaped) {
            resultBuilder.append(element).append(" ");
        }

        // Convert StringBuilder to String and return
        return resultBuilder.toString();
    }
}
