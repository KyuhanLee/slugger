package slugger;

import java.util.Iterator;

import it.unimi.dsi.fastutil.ints.*;
import it.unimi.dsi.fastutil.shorts.ShortArrayList;

public class DTree implements Iterable<Long>{
    public int num;
//    public byte height;
    public DTree left = this;
    public DTree right = this;
    public DTree parent = this;

    public IntArrayList indices = null;
    private IntArrayList cost = null;
    private ShortArrayList encoding = null;

    public IntArrayList nodes;
    public IntArrayList edges = null;

    private long totalCost;

    //Internal node
    public DTree(int num, DTree left, DTree right){
        this.num = num;
        this.left = left; this.left.parent = this;
        this.right = right; this.right.parent = this;
//        this.height = (byte) (Math.max(left.height, right.height) + 1);

        this.indices = new IntArrayList(1);
        this.cost = new IntArrayList(1);
        this.encoding = new ShortArrayList(1);

        this.indices.add(-1);
        this.cost.add(-1);
        this.encoding.add((short)0);

        if(this.left.nodes.size() > this.right.nodes.size()){
            this.nodes = new IntArrayList(this.left.nodes);
//            this.nodes = this.left.nodes;
            this.nodes.addAll(this.right.nodes);
        }else{
            this.nodes = new IntArrayList(this.right.nodes);
//            this.nodes = this.right.nodes;
            this.nodes.addAll(this.left.nodes);
        }
//        this.left.nodes = null;
//        this.right.nodes = null;
    }

    // Leaf node
    public DTree(int num, IntArrayList adj){
        this.num = num;
//        this.height = 0;
        int len = adj.size();

        this.indices = new IntArrayList(len+1);
        this.cost = new IntArrayList(len+1);
        this.encoding = new ShortArrayList(len+1);
        this.indices.add(-1);
        this.cost.add(-1);
        this.encoding.add((short)0);
        for(int i: adj){
            this.indices.add(i);
            this.cost.add(1);
            this.encoding.add((num <= i) ? (short)0x00ff : (short)0xff00);
        }
        this.nodes = new IntArrayList(1);
        this.nodes.add(num);
        this.totalCost = len;
    }

    public long getTotalCost(){
        return totalCost;
    }

    public int getKthIndex(int k){
        if(this.indices.size() == 0) return -1;
        return this.indices.getInt(k);
    }

    public int getKthCost(int k){
        return this.cost.getInt(k);
    }

    public short getKthEncoding(int k){
        short val = this.encoding.getShort(k);
        // return (val < 0) ? (~val) : val;
        return val;
    }

    public boolean getKthDirection(int k){
        return !(this.encoding.getShort(k) < 0);
    }

    public int length(){
        return this.indices.size();
    }

    public boolean is_leaf(){
        return (this.left.num == this.num);
    }

    public boolean is_root(){
        return (this.parent.num == this.num);
    }

    public void createLink(int U, int _encoding, boolean _direction){
        if(U == this.num){
            this.indices.set(0, this.num);
            this.encoding.set(0, (short)_encoding);
        }else{
            this.indices.add(U);
            this.encoding.add((short)(_direction ? _encoding : ~_encoding));
        }
    }

    public void removeLink(int k){
        if((!is_leaf()) && (k == 0)) return;
        int len = this.length();
        this.totalCost -= this.cost.getInt(k);
        if(k < len - 1){
            this.indices.set(k, this.indices.getInt(len-1));
            this.cost.set(k, this.cost.getInt(len-1));
            this.encoding.set(k, this.encoding.getShort(len-1));
        }
        this.indices.popInt();
        this.cost.popInt();
        this.encoding.popShort();
    }

    public void updateCost(int U, int _cost){
        if(U == this.num){
            if(this.indices.getInt(0) != this.num) System.out.println("update_cost??");
            this.cost.set(0, _cost);
        }else{
            if(this.indices.getInt(this.length() - 1) != U) System.out.println("update_cost??");
            this.cost.add(_cost);
        }
        this.totalCost += _cost;
    }

    public void updateSelfEncoding(int _encoding){
        if(this.indices.getInt(0) != this.num){
            //System.out.println("update selfenc??");
            this.indices.set(0, this.num);
            this.cost.set(0, 0);
        }
        this.encoding.set(0, (short)_encoding);
    }

    public void reset(){
        indices = null;
        cost = null;
        encoding = null;
        this.totalCost = 0;
    }

    public Iterator<Long> iterator() {
        return new EntryIterator(this);
    }
}

class EntryIterator implements Iterator<Long> {
    private DTree entries = null;

    public EntryIterator(DTree entries){
    }

    @Override
    public boolean hasNext() {
        return false;
    }

    @Override
    public Long next() {
        return null;
    }

}