package slugger;

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntOpenHashSet;
import jdk.jshell.spi.ExecutionControl;
import java.io.IOException;
import java.util.concurrent.ThreadLocalRandom;

public class SummaryGraphModule implements IncrementalInterface{
    // Core data structure
    public Int2IntOpenHashMap vmap = new Int2IntOpenHashMap(0);
    private IntArrayList degcnt = new IntArrayList(0);
    protected IntOpenHashSet[] adjSet;
    protected int n = 0, m = 0;

    // helper
    private final ThreadLocalRandom random;
    
    // argument
    protected boolean directed;
    protected boolean flag;

    public SummaryGraphModule(boolean directed){
        this.random = ThreadLocalRandom.current();
        this.directed = directed;
        this.flag = false;
    }

    public void setFlag(boolean new_flag) {
        flag = new_flag;
        if(new_flag){
            adjSet = new IntOpenHashSet[n];
            for(int i=0;i<n;i++) adjSet[i] = new IntOpenHashSet(degcnt.getInt(i));
            degcnt = null;
        }else{
            vmap = new Int2IntOpenHashMap(0);
            degcnt = new IntArrayList(0);
            adjSet = null;
            n = 0; m = 0;
        }
    }

    public void addVertex(int v) {
        int idx = vmap.getOrDefault(v, -1);
        if(idx < 0){
            idx = n;
            vmap.addTo(v, n);
            degcnt.add(0);
            n += 1;
        }
        degcnt.set(idx, degcnt.getInt(idx) + 1);
    }

    @Override
    public void processAddition(final int _src, final int _dst){
        if(flag){
            int src = vmap.get(_src);
            int dst = vmap.get(_dst);
            adjSet[src].add(dst);
            adjSet[dst].add(src);
        }else{
            addVertex(_src);
            addVertex(_dst);
            m++;
        }
    }

    public void processBatch() throws IOException {
        try {
            throw new ExecutionControl.NotImplementedException("processBatch: NOT_IMPLEMENTED");
        } catch (ExecutionControl.NotImplementedException e) {
            e.printStackTrace();
            System.exit(-1);
        }
    }

    protected int randInt(final int from, final int to){
        // return generated random number in [from, to] (close interval)
        return from + random.nextInt(to - from + 1);
    }
}
