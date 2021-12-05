package slugger;

import it.unimi.dsi.fastutil.ints.*;
import it.unimi.dsi.fastutil.objects.ObjectArrayList;

public class FinalTree {
    public int num;
    public FinalTree parent;
    public ObjectArrayList<FinalTree> children;
    
    public IntOpenHashSet edges;
    public int globalTreeCost = 0, globalNodeCount = 0;
    public int totalIntermediateCnt = 0;
    public int fixed = 0;

    public Int2LongOpenHashMap smallPi = null;
    public Int2LongOpenHashMap edgeCount = null;
    public Int2ObjectOpenHashMap<IntOpenHashSet> treeCost = null;
    public Int2IntOpenHashMap edgeCost = null;
    public IntOpenHashSet noDecision = null;
    public Int2LongOpenHashMap piArgMax = null;
    public Int2LongOpenHashMap argVal = null;

    private void seekChilds(DTree node){
        if(node.edges != null || node.is_leaf()){
            FinalTree newnode = new FinalTree(node);
            children.add(newnode);
            newnode.parent = this;
            globalTreeCost += (newnode.globalTreeCost + ((node.is_leaf()) ? 0 : 1));
            globalNodeCount += newnode.globalNodeCount;
            totalIntermediateCnt += newnode.totalIntermediateCnt;
            return;
        }
        seekChilds(node.left);
        seekChilds(node.right);
    }

    //Internal node
    public FinalTree(DTree node){//, FinalTree _superParent){
        parent = null;
        //superParent = (_superParent == null) ? this : _superParent;
        num = node.num;
        if(node.is_leaf()){
            children = null;
            globalNodeCount = 1;
        }else{
            children = new ObjectArrayList<>(2);
            seekChilds(node.left);
            seekChilds(node.right);
        }
        if(node.edges != null) edges = new IntOpenHashSet(node.edges);
        totalIntermediateCnt += 1;
    }

    public boolean addEdge(int v){
        if(edges == null){
            edges = new IntOpenHashSet(1);
        }else if(edges.contains(~v)){
            edges.remove((~v));
            return false;
        }else if(edges.contains(v)){
            System.out.println("UNEXPECTED...");
            return true;
        }
        edges.add(v);
        return true;
    }

    public void updateChildren(){
        int idx = 0;
        while(idx < children.size()){
            FinalTree node = children.get(idx);
            if(node.children == null || node.edges.size() > 0){
                idx += 1;
                continue;
            }
            children.set(idx, children.get(children.size()-1));
            children.pop();
            for(FinalTree v: node.children){
                v.parent = this;
                children.add(v);
            }
        }

        globalTreeCost = 0; globalNodeCount = 0; totalIntermediateCnt = 1;
        for(FinalTree v: children){
            globalTreeCost += (v.globalTreeCost + ((v.children == null) ? 0 : 1));
            globalNodeCount += v.globalNodeCount;
            totalIntermediateCnt += v.totalIntermediateCnt;
        }
    }
}
