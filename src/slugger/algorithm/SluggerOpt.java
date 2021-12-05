package slugger.algorithm;

import it.unimi.dsi.fastutil.ints.*;
import it.unimi.dsi.fastutil.longs.LongArrayFIFOQueue;
import it.unimi.dsi.fastutil.longs.LongArrayList;
import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import jdk.jshell.spi.ExecutionControl;
import slugger.DTree;
import slugger.FinalTree;
import slugger.SummaryGraphModule;

import java.io.*;
import java.time.Duration;
import java.time.Instant;
import java.util.Arrays;
import java.util.HashMap;

import static java.lang.Integer.min;

public class SluggerOpt extends SummaryGraphModule{

    private int T = 20; // number of iterations
    private IntArrayList[] adjList;
    private int treeCost = 0;

    private int[] h;
    private int[] shingles;
    private ObjectArrayList<IntArrayList> groups;
    private int threshold = 500, max_step = 10;
    private int[] candidates; private int sn;
    private long[][] sep; private int sepn;
    private Instant _start = Instant.now();

    private int[] fullMap = {255, 85, 170, 5, 10, 80, 160, 15, 240, 3, 12, 48, 192, 1, 2, 4, 8, 16, 32, 64, 128};
    private int[] selfFullMap = {1023, 127, 1016, 7, 896, 120, 3 + 24, 6 + 96, 40 + 384, 80 + 768, 3, 6, 40, 80, 24, 96, 384, 768, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512};
    private int[] minMap = {15, 5, 10, 1, 2, 4, 8, 3, 12};
    private int[] selfMinMap = {7, 3, 6, 1, 4, 2};
    private int[] selfMinCost = {0,1,1,1,1,2,1,1};
    private int[] minCost = {0,1,1,1,1,1,2,2,1,2,1,2,1,2,2,1};

    private int[] bitcnt = new int[1024];
    private int[] cost = new int[256], selfCost = new int[1024];
    private int[] fours = new int[256], threes = new int[1024];

    private LongArrayList[] bestMaps = new LongArrayList[256], selfBestMaps = new LongArrayList[1024];
    private long[][] dropMaps = new long[256][16];
    private LongArrayList[][] selfDropMaps = new LongArrayList[1024][16];

    private long[] reduction = new long[threshold];
    private int[] recentCost;
    private int[] recentIdx;
    private short[] recentEncoding;

    private DTree[] ref;

    private int[][] diff = new int[16][16];
    private int[] twos = new int[65536 + 1];
    private int[] flip = {0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15};
    private IntArrayList[] selfloop_mark;

    private int[] selfEncodeSrcPosition = {0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 3, 3, 4, 4, 5, 5, 6};
    private int[] selfEncodeDstPosition = {0, 1, 2, 1, 2, 2, 3, 4, 5, 6, 3, 4, 5, 6, 3, 4, 5, 6, 3, 4, 4, 5, 6, 5, 6, 5, 6, 6};
    private int[] encodeSrcPosition = {0, 0, 0, 1, 1, 2, 2, 1, 2, 3, 4, 5, 6, 3, 3, 4, 4, 5, 5, 6, 6};
    private int[] encodeDstPosition = {0, 1, 2, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 1, 2, 1, 2};
    private int newSupernode;

    private Int2IntOpenHashMap[] checker;

    private long reduced = 0;
    private FinalTree[] fnodes;
    private int[] superParent;

    public SluggerOpt(boolean directed){
        super(directed);
        if(directed){
            try {
                throw new ExecutionControl.NotImplementedException("Directed version is NOT_IMPLEMENTED");
            } catch (ExecutionControl.NotImplementedException e) {
                e.printStackTrace();
                System.exit(-1);
            }
        }
    }

    private void divideInner(int step) {
        int me = step % 2;
        if(step == max_step){
            for(int ii=0;ii<sepn;ii++){
                int s = (int)(sep[me][ii] >> 32), e = (int)(sep[me][ii] & 0x7FFFFFFFL);
                for(int i=s;i<=e;i+=threshold){
                    if(i + (threshold - 1) <= e){
                        groups.add(new IntArrayList(candidates, i, threshold));
                    }else{
                        groups.add(new IntArrayList(candidates, i, (e-i+1)));
                    }
                }
            }
            return;
        }
        for (int i = 0; i < n; i++) {
            int target = randInt(0, i);
            // if target == i -> h[i] = h[i]; h[i] = i;
            // if target < i -> h[i] = h[target]; h[target] = i;
            h[i] = h[target];
            h[target] = i;
        }
        int nxt_sepn = 0;
        for(int ii=0;ii<sepn;ii++){
            int s = (int)(sep[me][ii] >> 32), e = (int)(sep[me][ii] & 0x7FFFFFFFL);
            for(int i=s;i<=e;i++){
                final int A = candidates[i];
                int minHash = 0x7FFFFFFF;
                for(int v: ref[A].nodes){
                    minHash = min(minHash, h[v]);
                    for(int u: adjList[v]){
                        minHash = min(minHash, h[u]);
                    }
                }
                shingles[A] = minHash;
            }
            IntArrays.parallelQuickSort(candidates, s, e + 1, new IntComparator() {
                @Override
                public int compare(int i, int i1) {
                    return Integer.compare(shingles[i], shingles[i1]);
                }
            });
            int prv = s;
            for(int i=s+1;i<=e;i++){
                if(shingles[candidates[i]] != shingles[candidates[i-1]]){
                    if(i - prv <= threshold){
                        groups.add(new IntArrayList(candidates, prv, i-prv));
                    }else{
                        sep[1-me][nxt_sepn++] = (((long)prv) << 32) + (i-1);
                    }
                    prv = i;
                }
            }
            if((e + 1) - prv <= threshold){
                groups.add(new IntArrayList(candidates, prv, (e+1) - prv));
            }else{
                sep[1-me][nxt_sepn++] = (((long)prv) << 32) + e;
            }
        }
        if(nxt_sepn > 0){
            sepn = nxt_sepn;
            divideInner(step + 1);
        }
    }

    private void divide() {
        // Input: input graph G = (V, E), current supernodes S
        // Output: disjoint groups of supernodes (shingle)
        for (int i = 1; i < sn; i++) {
            int target = randInt(0, i);
            if(i == target) continue;
            int tmp = h[i];
            h[i] = h[target];
            h[target] = tmp;
        }
        sepn = 1;
        sep = new long[2][(sn + threshold + threshold) / threshold];
        sep[0][0] = sn-1;
        groups = new ObjectArrayList<>(n / threshold);
        divideInner(0);
    }

    private void putEdge(DTree A, DTree B, boolean sign){
        if(A.edges == null) A.edges = new IntArrayList(1);
        if(B.edges == null) B.edges = new IntArrayList(1);
        A.edges.add(sign ? B.num : (~B.num));
        if(A.num != B.num) B.edges.add(sign ? A.num : (~A.num));
    }

    private void encode(long mapping, DTree A, DTree U, boolean last){
        DTree[] srcs = {A, A.left, A.right, A.left.left, A.left.right, A.right.left, A.right.right};
        DTree[] dsts = {U, U.left, U.right};

        int pos = ((int)(mapping >> 21)) & (last ? (-1) : (-512)), neg = ((int)(mapping & ((long)(1 << 21) - 1))) & (last ? (-1) : (-512));
        while(pos > 0){
            int target = (pos & (-pos));
            target = (target < 65536) ? twos[target] : (twos[target >> 16] + 16);
            putEdge(srcs[encodeSrcPosition[target]], dsts[encodeDstPosition[target]], true);
            pos = pos & (pos-1);
        }
        while(neg > 0){
            int target = (neg & (-neg));
            target = (target < 65536) ? twos[target] : (twos[target >> 16] + 16);
            putEdge(srcs[encodeSrcPosition[target]], dsts[encodeDstPosition[target]], false);
            neg = neg & (neg-1);
        }
    }

    private void selfEncode(long mapping, DTree A, boolean last){
        DTree[] blocks = {A, A.left, A.right, A.left.left, A.left.right, A.right.left, A.right.right};

        int pos = ((int)(mapping >> 28)) & (last ? (-1) : (-64)), neg = ((int)(mapping & ((long)(1 << 28) - 1))) & (last ? (-1) : (-64));
        while(pos > 0){
            int target = (pos & (-pos));
            target = (target < 65536) ? twos[target] : (twos[target >> 16] + 16);
            putEdge(blocks[selfEncodeSrcPosition[target]], blocks[selfEncodeDstPosition[target]], true);
            pos = pos & (pos-1);
        }
        while(neg > 0){
            int target = (neg & (-neg));
            target = (target < 65536) ? twos[target] : (twos[target >> 16] + 16);
            putEdge(blocks[selfEncodeSrcPosition[target]], blocks[selfEncodeDstPosition[target]], false);
            neg = neg & (neg-1);
        }
    }

    private void finEncode(int A, int B, int U, int A_best_enc, int B_best_enc){
        if(A_best_enc >= 0) encode(dropMaps[A_best_enc >> 4][A_best_enc & 15], ref[A], ref[U], false);
        else encode(dropMaps[(~A_best_enc) >> 4][flip[(~A_best_enc) & 15]], ref[U], ref[A], false);
        if(B_best_enc >= 0) encode(dropMaps[B_best_enc >> 4][B_best_enc & 15], ref[B], ref[U], false);
        else encode(dropMaps[(~B_best_enc) >> 4][flip[(~B_best_enc) & 15]], ref[U], ref[B], false);
    }

    private void sfinEncode(int A, int B, int AA_best_enc, int AB_best_enc, int BB_best_enc) {
        selfEncode(selfDropMaps[AA_best_enc >> 4][AA_best_enc & 15].getLong(0), ref[A], false);
        if (AB_best_enc >= 0) encode(dropMaps[AB_best_enc >> 4][AB_best_enc & 15], ref[A], ref[B], false);
        else encode(dropMaps[(~AB_best_enc) >> 4][flip[(~AB_best_enc) & 15]], ref[B], ref[A], false);
        selfEncode(selfDropMaps[BB_best_enc >> 4][BB_best_enc & 15].getLong(0), ref[B], false);
    }

    private long blockCost(int A, int B, int U, int idx, DTree target_ref) {
        int A_enc = (recentCost[U] < 0) ? 0: recentEncoding[U];
        boolean A_dir = !(A_enc < 0);
        int B_enc = (idx < 0) ? 0 : ref[B].getKthEncoding(idx);
        boolean B_dir = !(B_enc < 0);

        A_enc = A_dir ? A_enc : (~A_enc);
        B_enc = B_dir ? B_enc : (~B_enc);

        int bestDelta = -100000000;
        int argmax = 0;

        // self block
        if(A == U){
            int BB_enc = (ref[B].getKthIndex(0) == B) ? ref[B].getKthEncoding(0) : 0;
            int A_query = (ref[A].left.left.is_leaf() ? 1 : 0) | (ref[A].left.right.is_leaf() ? 2 : 0) | (ref[A].right.left.is_leaf() ? 4 : 0) | (ref[A].right.right.is_leaf() ? 8 : 0);
            A_query |= (ref[A].left.is_leaf() ? 16 : 0) | (ref[A].right.is_leaf() ? 32 : 0) | (ref[A].is_leaf() ? 64 : 0);
            int B_query = (ref[B].left.left.is_leaf() ? 1 : 0) | (ref[B].left.right.is_leaf() ? 2 : 0) | (ref[B].right.left.is_leaf() ? 4 : 0) | (ref[B].right.right.is_leaf() ? 8 : 0);
            B_query |= (ref[B].left.is_leaf() ? 16 : 0) | (ref[B].right.is_leaf() ? 32 : 0) | (ref[B].is_leaf() ? 64 : 0);
            for(int _i: selfloop_mark[A_query]){
                for(int _k: selfloop_mark[B_query]){
                    int AAs = threes[A_enc];
                    int ABs = fours[B_enc];
                    int BBs = threes[BB_enc];
                    int _AAs = AAs;
                    while(_AAs > 0){
                        int i = twos[_AAs & (-_AAs)];
                        int _ABs = ABs;
                        while(_ABs > 0){
                            int j = (!B_dir) ? twos[_ABs & (-_ABs)] : flip[twos[_ABs & (-_ABs)]];
                            int _BBs = BBs;
                            while(_BBs > 0){
                                int k = twos[_BBs & (-_BBs)];
                                int costid = (i | ((_i & 7) / 7) | ((_i & 896) / 224) | (((_i & 1023) / 1023) * 7));
                                costid ^= (j << 3);
                                costid ^= ((k | ((_k & 7) / 7) | ((_k & 896) / 224) | (((_k & 1023) / 1023) * 7)) << 7);
                                int delta = selfMinCost[i] + minCost[j] + selfMinCost[k] - selfCost[costid];
                                if(delta > bestDelta && selfDropMaps[A_enc | _i][costid & 7] != null && selfDropMaps[BB_enc | _k][(costid >> 7) & 7] != null){
                                    bestDelta = delta;
                                    argmax = costid^(_i << 10)^(_k << 20);
                                }
                                _BBs = _BBs & (_BBs - 1);
                            }
                            _ABs = _ABs & (_ABs - 1);
                        }
                        _AAs = _AAs & (_AAs - 1);
                    }
                }
            }
            if(target_ref != null){
                A_enc |= ((argmax >> 10) & 1023);
                BB_enc |= (argmax >> 20);
                ref[A].updateSelfEncoding(A_enc);
                ref[B].updateSelfEncoding(BB_enc);

                int AA_best_enc = (A_enc << 4) ^ (argmax & 7);
                int AB_best_enc = (B_enc << 4) ^ ((argmax >> 3) & 15);
                int BB_best_enc = (BB_enc << 4) ^ ((argmax >> 7) & 7);
                sfinEncode(A, B, AA_best_enc, (!B_dir) ? AB_best_enc : (~AB_best_enc), BB_best_enc);
                target_ref.createLink(newSupernode, (argmax & 1023), true);
            }
            return -bestDelta;
        }
        // block
        else{
            bestDelta = 0;
            int _AUs = fours[A_enc];
            int BUs = fours[B_enc];
            int _BUs = BUs;
            argmax = (A_dir ? twos[_AUs & (-_AUs)] : flip[twos[_AUs & (-_AUs)]]) + ((B_dir ? twos[_BUs & (-_BUs)] : flip[twos[_BUs & (-_BUs)]]) << 4);
            while(_AUs > 0){
                int i = A_dir ? twos[_AUs & (-_AUs)] : flip[twos[_AUs & (-_AUs)]];
                _BUs = BUs;
                while(_BUs > 0){
                    int j = B_dir ? twos[_BUs & (-_BUs)] : flip[twos[_BUs & (-_BUs)]];
                    if(diff[i][j] > 0){
                        bestDelta = diff[i][j];
                        argmax = i ^ (j << 4);
                        break;
                    }
                    _BUs = _BUs & (_BUs - 1);
                }
                if(bestDelta > 0) break;
                _AUs = _AUs & (_AUs - 1);
            }
            if(target_ref != null){
                int A_best_enc = (A_enc << 4) ^ (argmax & 15);
                int B_best_enc = (B_enc << 4) ^ (argmax >> 4);
                finEncode(A, B, U, A_dir ? A_best_enc : (~A_best_enc), B_dir ? B_best_enc : (~B_best_enc));
                target_ref.createLink(U, argmax, true);
                ref[U].createLink(newSupernode, argmax, false);
            }
            return -bestDelta;
        }
    }

    private long getAfterCost(int A, int B) {
        long ans = 0;
        int _i = (ref[B].getKthIndex(0) < 0) ? 1 : 0;
        recentIdx[A] = -1;
        while(_i < ref[B].length()){
            int U = ref[B].getKthIndex(_i);
            if(U == A || U == B){
                recentIdx[U] = _i;
                _i++;
                continue;
            }
            if(!ref[U].is_root()){
                ref[B].removeLink(_i);
                continue;
            }

            long merged_cost = ((recentCost[U] < 0) ? 0 : recentCost[U]) + ref[B].getKthCost(_i);
            recentIdx[U] = _i;
            merged_cost += blockCost(A, B, U, _i, null);
            ans += merged_cost;
            _i++;
        }

        // handle self-loop first
        if((recentCost[A] >= 0) || (recentCost[B] >= 0) || ref[B].getKthIndex(0) == B){
            long merged_cost = ((recentCost[A] < 0) ? 0 : recentCost[A]) + ((recentCost[B] < 0) ? 0 : recentCost[B]) + ((ref[B].getKthIndex(0) == B) ? ref[B].getKthCost(0) : 0);
            merged_cost += blockCost(A, B, A, recentIdx[A], null);
            ans += merged_cost;
        }
        if(recentIdx[A] < 0) recentIdx[A] = 0;

        _i = (ref[A].getKthIndex(0) < 0) ? 1 : 0;
        while(_i < ref[A].length()){
            int U = ref[A].getKthIndex(_i);
            if(U == A || U == B){
                _i++;
                continue;
            }
            if(!ref[U].is_root()){
                ref[A].removeLink(_i);
                continue;
            }
            if(recentIdx[U] < ref[B].length() && ref[B].getKthIndex(recentIdx[U]) == U){
                _i++;
                continue;
            }
            long merged_cost = recentCost[U];
            merged_cost += blockCost(A, B, U, -1, null);
            ans += merged_cost;
            _i++;
        }
        return ans;
    }

    private int mergeInner(int A, int B) {

        if(!ref[A].is_leaf()) treeCost += 1;
        if(!ref[B].is_leaf()) treeCost += 1;
        ref[newSupernode] = new DTree(newSupernode, ref[A], ref[B]);

        recentIdx[A] = -1;
        int _i = (ref[B].getKthIndex(0) < 0) ? 1 : 0;
        while(_i < ref[B].length()){
            int U = ref[B].getKthIndex(_i);
            if(U == A || U == B){
                recentIdx[U] = _i;
                _i++;
                continue;
            }
            if(!ref[U].is_root()){
                ref[B].removeLink(_i);
                continue;
            }
            long merged_cost = ((recentCost[U] < 0) ? 0 : recentCost[U]) + ref[B].getKthCost(_i);
            recentIdx[U] = _i;
            merged_cost += blockCost(A, B, U, _i, ref[newSupernode]);
            ref[newSupernode].updateCost(U, (int)merged_cost);
            ref[U].updateCost(newSupernode, (int)merged_cost);
            _i++;
        }

        // handle self-loop first
        if((recentCost[A] >= 0) || (recentCost[B] >= 0) || ref[B].getKthIndex(0) == B){
            long merged_cost = ((recentCost[A] < 0) ? 0 : recentCost[A]) + ((recentCost[B] < 0) ? 0 : recentCost[B]) + ((ref[B].getKthIndex(0) == B) ? ref[B].getKthCost(0) : 0);
            merged_cost += blockCost(A, B, A, recentIdx[A], ref[newSupernode]);
            if(merged_cost > 0) ref[newSupernode].updateCost(newSupernode, (int)merged_cost);
        }
        if(recentIdx[A] < 0) recentIdx[A] = 0;

        _i = (ref[A].getKthIndex(0) < 0) ? 1 : 0;
        while(_i < ref[A].length()){
            int U = ref[A].getKthIndex(_i);
            if(U == A || U == B){
                _i++;
                continue;
            }
            if(!ref[U].is_root()){
                ref[A].removeLink(_i);
                continue;
            }
            if(recentIdx[U] < ref[B].length() && ref[B].getKthIndex(recentIdx[U]) == U){
                _i++;
                continue;
            }
            long merged_cost = recentCost[U];
            merged_cost += blockCost(A, B, U, -1, ref[newSupernode]);
            ref[newSupernode].updateCost(U, (int)merged_cost);
            ref[U].updateCost(newSupernode, (int)merged_cost);
            _i++;
        }
        _i = (ref[A].getKthIndex(0) < 0) ? 1 : 0;
        while(_i < ref[A].length()){
            recentCost[ref[A].getKthIndex(_i)] = -1;
            _i++;
        }
        ref[A].reset();
        ref[B].reset();
        return newSupernode;
    }

    private void merge(int iter){
        sn = 0;
        for(IntArrayList _Q: groups){
            IntArrayList Q = new IntArrayList(_Q);
            int sz = Q.size();
            while(sz > 1){
                int randIdx = randInt(0, sz-1);
                int A = Q.getInt(randIdx);
                Q.set(randIdx, Q.getInt(sz-1));
                Q.popInt(); sz -= 1;
                double maxSaving = -1.0;
                int argMax = -1;

                int _i = (ref[A].getKthIndex(0) < 0) ? 1 : 0;
                while(_i < ref[A].length()){
                    int idx = ref[A].getKthIndex(_i);
                    if(!ref[idx].is_root()){
                        ref[A].removeLink(_i);
                        continue;
                    }
                    recentCost[idx] = ref[A].getKthCost(_i);
                    recentEncoding[idx] = ref[A].getKthEncoding(_i);
                    _i++;
                }

                for(int i=0;i<sz;i++){
                    int B = Q.getInt(i);
                    long afterCost = getAfterCost(A, B);
                    long beforeCost = ref[A].getTotalCost() + ref[B].getTotalCost() - ((recentCost[B] < 0) ? 0 : recentCost[B]);
                    reduction[i] = beforeCost - afterCost;
                    double tmpSaving = reduction[i] / ((double)beforeCost);
                    if((tmpSaving > maxSaving) && (reduction[i]>=2)){
                        maxSaving = tmpSaving;
                        argMax = i;
                    }
                }

                double threshold = (iter < T) ? (1.0 / (double) (1 + iter)) : 0;
                if(maxSaving >= threshold){
                    reduced += reduction[argMax];
                    int B = Q.getInt(argMax);
                    Q.set(argMax, Q.getInt(sz-1));
                    mergeInner(A, B);
                    Q.set(sz-1, newSupernode);
                    newSupernode++;
                }else{
                    candidates[sn++] = A;
                    _i = (ref[A].getKthIndex(0) < 0) ? 1 : 0;
                    while(_i < ref[A].length()){
                        recentCost[ref[A].getKthIndex(_i)] = -1;
                        _i++;
                    }
                }
            }
            if(sz == 1) candidates[sn++] = Q.getInt(0);
        }
        groups.clear();
    }

    private void finalTouch(){
        for(int A=0; A<newSupernode; A++){
            if(ref[A].is_root()){
                int _i = (ref[A].getKthIndex(0) < 0) ? 1 : 0;
                while(_i < ref[A].length()){
                    int target = ref[A].getKthIndex(_i);
                    if(!ref[target].is_root()){
                        ref[A].removeLink(_i);
                        continue;
                    }
                    int _enc = ref[A].getKthEncoding(_i);
                    boolean direction = !(_enc < 0);
                    int enc = (direction) ? _enc : (~_enc);
                    if(direction){
                        if(A == target){
                            long mapping = selfDropMaps[enc][twos[threes[enc] & (-threes[enc])]].getLong(0);
                            selfEncode(mapping, ref[A], true);
                        }else{
                            long mapping = dropMaps[enc][twos[fours[enc] & (-fours[enc])]];
                            encode(mapping, ref[A], ref[target], true);
                        }
                    }
                    _i++;
                }
            }
        }
    }

    @Override
    public void processBatch() throws IOException {
        System.out.println("|V|: " + n);

        adjList = new IntArrayList[n];
        newSupernode = n;
        int edgeCnt = 0;
        for(int i=0;i<n;i++){
            adjList[i] = new IntArrayList(adjSet[i]);
            for(int j=0;j<adjList[i].size();j++){
                edgeCnt += 1;
                if(adjList[i].getInt(j) == i) edgeCnt += 1;
            }
            adjSet[i] = null;
        }
        adjSet = null;

        System.out.println(edgeCnt / 2);
        int _oldEdgeCnt = edgeCnt;


        // for divide
        h = new int[n];
        shingles = new int[n+n-1];
        candidates = new int[n+1];

        ref = new DTree[n + n - 1];
        for(int i=0;i<1024;i++){
            int cnt = 0, ii = i;
            while(ii > 0){
                ii = ii & (ii-1);
                cnt += 1;
            }
            bitcnt[i] = cnt;
        }

        buildMap();
        buildSMap();
        for(int i=0; i<16;i++){
            for(int j=0; j<16; j++){
                diff[i][j] = minCost[i] + minCost[j] - cost[i + 16*j];
            }
        }
        for(int i=0;i<16;i++){
            twos[1 << i] = i;
        }

        recentCost = new int[n + n - 1];
        recentEncoding = new short[n + n - 1];
        recentIdx = new int[n + n - 1];

        for(int i=0;i<n+n-1;i++){
            recentCost[i] = -1;
            recentIdx[i] = 0;
        }

        for(int i=0;i<n;i++){
            ref[i] = new DTree(i, adjList[i]);
            candidates[i] = i;
        }
        sn = n;

        // System.out.println("READY! " + Duration.between(_start, Instant.now()).toMillis() / 1000.0 + "s.");
        for(int iter=1;iter<=T;iter++){
            //System.out.println("Iter #" + iter);
            divide();
            merge(iter);
        }
        finalTouch();

        edgeCnt = 0;
        for(int i=0;i<newSupernode;i++){
            if(ref[i].edges != null){
                edgeCnt += ref[i].edges.size();
                if(ref[i].edges.contains(i) || ref[i].edges.contains((~i))){
                    edgeCnt += 1;
                }
            }
        }

        fnodes = new FinalTree[newSupernode];

        int reducedEdgeCnt = 0;
        int reducedTreeCost = 0, reducedNodeCounts = 0, reducedSupernodeCounts = 0, reducedIntermediateNodes = 0, expectedIntermeidateCount = 0, singletonSupernodeCounts = 0;


        // Step 1
        for(int i=newSupernode-1;i>=0;i--){
            if(ref[i].is_root()){
                if(ref[i].edges == null){
                    ref[i].left.parent = ref[i].left;
                    ref[i].right.parent = ref[i].right;
                    continue;
                }else{
                    fnodes[i] = new FinalTree(ref[i]);
                    reducedTreeCost += fnodes[i].globalTreeCost;
                    reducedNodeCounts += fnodes[i].globalNodeCount;
                    if(fnodes[i].globalNodeCount == 1) singletonSupernodeCounts += 1;
                    expectedIntermeidateCount += fnodes[i].totalIntermediateCnt;
                    reducedSupernodeCounts += 1;
                    reducedIntermediateNodes += 1;
                    reducedEdgeCnt += fnodes[i].edges.size();
                    if(fnodes[i].edges != null && (fnodes[i].edges.contains(i) || fnodes[i].edges.contains(~i))) reducedEdgeCnt += 1;
                    FinalTree target_node = fnodes[i];
                    IntArrayList stk = new IntArrayList(1);
                    stk.add(0);
                    while(true){
                        if(target_node.children == null || target_node.children.size() == stk.topInt()){
                            stk.popInt();
                            target_node = target_node.parent;
                            if(stk.isEmpty()) break;
                            stk.set(stk.size()-1, stk.topInt() + 1);
                        }else{
                            target_node = target_node.children.get(stk.topInt());
                            fnodes[target_node.num] = target_node;
                            stk.add(0);
                            reducedIntermediateNodes += 1;
                            reducedEdgeCnt += ((target_node.edges == null) ? 0 : target_node.edges.size());
                            if(target_node.edges != null && (target_node.edges.contains(target_node.num) || target_node.edges.contains(~target_node.num))) reducedEdgeCnt += 1; //self-loop
                        }
                    }
                }
            }
        }


        // Step 2
        for(int i=newSupernode-1;i>=0;i--){
            if(fnodes[i] != null && fnodes[i].parent == null && fnodes[i].children != null && fnodes[i].edges.size() <= 1){
                if(fnodes[i].edges.size() == 1){
                    int uniqueIdx = fnodes[i].edges.iterator().nextInt();
                    if(uniqueIdx == i || uniqueIdx == (~i)) continue;
                    if(uniqueIdx >= 0){
                        fnodes[uniqueIdx].addEdge((~i));
                        for(FinalTree v: fnodes[i].children){
                            v.addEdge(uniqueIdx);
                            fnodes[uniqueIdx].addEdge(v.num);
                        }
                    }else{
                        fnodes[(~uniqueIdx)].addEdge(i);
                        for(FinalTree v: fnodes[i].children){
                            v.addEdge(uniqueIdx);
                            fnodes[(~uniqueIdx)].addEdge((~(v.num)));
                        }
                    }
                }
                for(FinalTree v: fnodes[i].children){
                    v.parent = null;
                }
                fnodes[i] = null;
            }
        }

        // int optimizedEdgeCnt = 0;
        // int optimizedTreeCost = 0, optimizedNodeCounts = 0, optimizedSupernodeCounts = 0, optimizedIntermediateNodes = 0, optimizedIntermeidateCount = 0, optimizedSingletonSupernodeCounts = 0;

        // for(int i=newSupernode-1;i>=0;i--){
        //     if(fnodes[i] == null) continue;
        //     if(fnodes[i].parent == null){
        //         optimizedTreeCost += fnodes[i].globalTreeCost;
        //         optimizedNodeCounts += fnodes[i].globalNodeCount;
        //         if(fnodes[i].globalNodeCount == 1) optimizedSingletonSupernodeCounts += 1;
        //         optimizedIntermeidateCount += fnodes[i].totalIntermediateCnt;
        //         optimizedSupernodeCounts += 1;
        //     }
        //     optimizedIntermediateNodes += 1;
        //     optimizedEdgeCnt += ((fnodes[i].edges == null) ? 0 : fnodes[i].edges.size());
        //     if(fnodes[i].edges != null && (fnodes[i].edges.contains(i) || fnodes[i].edges.contains(~i))) optimizedEdgeCnt += 1;
        // }


        // Step 3
        LongArrayFIFOQueue determined = new LongArrayFIFOQueue();
        LongArrayList[] related = new LongArrayList[newSupernode];
        superParent = new int[newSupernode];

        for(int i=newSupernode-1;i>=0;i--){
            if(fnodes[i] == null) continue;
            superParent[i] = (fnodes[i].parent == null) ? i : superParent[fnodes[i].parent.num];
            if(superParent[i] == i){
                fnodes[i].edgeCount = new Int2LongOpenHashMap(1);
                fnodes[i].treeCost = new Int2ObjectOpenHashMap<IntOpenHashSet>(1);
                fnodes[i].edgeCost = new Int2IntOpenHashMap(1);
                fnodes[i].piArgMax = new Int2LongOpenHashMap(1);
                fnodes[i].argVal = new Int2LongOpenHashMap(1);
                fnodes[i].fixed = 1;
            }
            if(fnodes[i].children == null) fnodes[i].fixed = 1;
        }


        int cntt = 0, cntt2 = 0, _cntt2 = 0;
        for(int i=0;i<newSupernode;i++){
            if(fnodes[i] == null || fnodes[i].edges == null) continue;
            int sparent = superParent[i];
            for(int _e: fnodes[i].edges){
                cntt += 1;
                int e = (_e < 0) ? (~_e) : _e;
                int _sparent = superParent[e];

                if(!fnodes[sparent].argVal.containsKey(_sparent)){
                    cntt2 += 1 + ((sparent == _sparent) ? 1 : 0);
                }

                long smallPi = fnodes[i].globalNodeCount * (long)fnodes[e].globalNodeCount;
                if(i == e) smallPi = (smallPi - fnodes[i].globalNodeCount);
                long delta = ((_e < 0) ? (-1) : 1) * smallPi;
                _cntt2 += (int)delta;

                long argmaxPi = fnodes[sparent].argVal.getOrDefault(_sparent,  ((((long)i) << 31) + e));
                int max_u = (int)(argmaxPi >> 31), max_v = (int)(argmaxPi & 0x7FFFFFFFL);
                int lca_i = i, lca_e = e;
                while(max_u != lca_i){
                    if(max_u < lca_i) max_u = fnodes[max_u].parent.num;
                    else lca_i = fnodes[lca_i].parent.num;
                }
                while(max_v != lca_e){
                    if(max_v < lca_e) max_v = fnodes[max_v].parent.num;
                    else lca_e = fnodes[lca_e].parent.num;
                }
                fnodes[sparent].argVal.put(_sparent, ((((long)lca_i) << 31) + lca_e));
                fnodes[sparent].edgeCount.addTo(_sparent, delta);
                if(!fnodes[sparent].treeCost.containsKey(_sparent)) fnodes[sparent].treeCost.put(_sparent, new IntOpenHashSet(1));
                if(fnodes[i].fixed == 0) fnodes[sparent].treeCost.get(_sparent).add(i);
                if(fnodes[e].fixed == 0) fnodes[sparent].treeCost.get(_sparent).add(e);
                fnodes[sparent].edgeCost.addTo(_sparent, 1);
                if(i == e) fnodes[sparent].edgeCost.addTo(_sparent, 1);
            }
            if(i == sparent && fnodes[i].edgeCost.containsKey(i)){
                fnodes[i].edgeCost.put(i, fnodes[i].edgeCost.get(i) / 2);
            }
        }


        long cnt_Slugger = 0, cnt_SWeG = 0, cnt_left = 0;
        long small_sum = 0, large_sum = 0, count_sum = 0;
        for(int i=0;i<newSupernode;i++){
            if(fnodes[i] != null && fnodes[i].parent == null){ 
                fnodes[i].noDecision = new IntOpenHashSet(fnodes[i].edgeCount.keySet());
                for(int e: fnodes[i].edgeCount.keySet()){
                    if(i < e) continue;
                    long uv = fnodes[i].argVal.get(e);
                    int u = (int)(uv >> 31), v = (int)(uv & 0x7FFFFFFFL);
                    long smallPi = fnodes[u].globalNodeCount * (long)fnodes[v].globalNodeCount, edgeCount = fnodes[i].edgeCount.get(e);
                    int fcnt = (2 - fnodes[u].fixed - fnodes[v].fixed);
                    if(u == v){
                        smallPi = (smallPi - fnodes[v].globalNodeCount) / 2;
                        fcnt /= 2;
                    }
                    if(i == e) edgeCount /= 2;

                    long candidateCost = Long.min(edgeCount, (smallPi + fcnt) - edgeCount + 1), minSuperedgeCost = fnodes[i].edgeCost.get(e);
                    IntOpenHashSet treeCost = fnodes[i].treeCost.get(e);
                    for(int nbr: treeCost){
                        if(related[nbr] == null) related[nbr] = new LongArrayList(1);
                        related[nbr].add(((((long)i) << 31) + e));
                    }
                    small_sum += (int)smallPi; count_sum += minSuperedgeCost;
                    long lowerB;
                    if(candidateCost == ((smallPi + fcnt) - edgeCount + 1)){
                        lowerB = candidateCost - fcnt;
                    }else{
                        lowerB = edgeCount;
                    }
                    if(minSuperedgeCost + treeCost.size() <= lowerB){
                        // Slugger
                        determined.enqueue((((((long)i) << 31) + e) << 1) + 0);
                        fnodes[i].noDecision.remove(e);
                        fnodes[e].noDecision.remove(i);
                        cnt_Slugger++;
                    }else if(candidateCost <= minSuperedgeCost){
                        // SWeG
                        determined.enqueue((((((long)i) << 31) + e) << 1) + 1);
                        fnodes[i].noDecision.remove(e);
                        fnodes[e].noDecision.remove(i);
                        cnt_SWeG++;
                    }else{
                        cnt_left++;
                    }
                }
            }
        }


        while(!determined.isEmpty()){
            long _target = determined.dequeueLong();
            int mode = (int)(_target & 1L); _target = (_target >> 1);
            int U = (int)(_target >> 31), V = (int)(_target & 0x7FFFFFFFL);
            fnodes[U].edgeCost.put(V, mode);
            fnodes[V].edgeCost.put(U, mode);
            if(mode == 0){
                // Slugger
                for(int target: fnodes[U].treeCost.get(V)){
                    if(fnodes[target].fixed == 1) continue;
                    fnodes[target].fixed = 1;
                    for(long elem: related[target]){
                        int u = (int)(elem >> 31), v = (int)(elem & 0x7FFFFFFFL);
                        if((u != U) || (v != V)) fnodes[u].treeCost.get(v).remove(target);
                        if((u != V) || (v != U)) fnodes[v].treeCost.get(u).remove(target);
                    }
                    IntOpenHashSet newDetermined = new IntOpenHashSet(0);
                    int i = superParent[target];
                    for(int e: fnodes[i].noDecision){
                        long uv = fnodes[i].argVal.get(e);
                        int u = (int)(uv >> 31), v = (int)(uv & 0x7FFFFFFFL);
                        long smallPi = fnodes[u].globalNodeCount * (long)fnodes[v].globalNodeCount, edgeCount = fnodes[i].edgeCount.get(e);
                        int fcnt = (2 - fnodes[u].fixed - fnodes[v].fixed);
                        if(u == v){
                            smallPi = (smallPi - fnodes[v].globalNodeCount) / 2;
                            fcnt /= 2;
                        }
                        if(i == e) edgeCount /= 2;

                        long candidateCost = Long.min(edgeCount, (smallPi + fcnt) - edgeCount + 1), minSuperedgeCost = fnodes[i].edgeCost.get(e), treeCost = fnodes[i].treeCost.get(e).size();
                        long lowerB;
                        if(candidateCost == ((smallPi + fcnt) - edgeCount + 1)){
                            lowerB = candidateCost - fcnt;
                        }else{
                            lowerB = edgeCount;
                        }
                        if(minSuperedgeCost + treeCost <= lowerB){
                            // Slugger
                            determined.enqueue((((((long)i) << 31) + e) << 1) + 0);
                            newDetermined.add(e);
                            cnt_Slugger++;
                        }else if(candidateCost <= minSuperedgeCost){
                            // SWeG
                            determined.enqueue((((((long)i) << 31) + e) << 1) + 1);
                            newDetermined.add(e);
                            cnt_SWeG++;
                        }
                    }
                    for(int e: newDetermined){
                        fnodes[i].noDecision.remove(e);
                        fnodes[e].noDecision.remove(i);
                    }
                }
            }else{ //SWeG
                long _uv = fnodes[U].argVal.get(V);
                int _u = (int)(_uv >> 31), _v = (int)(_uv & 0x7FFFFFFFL);
                long _smallPi = fnodes[_u].globalNodeCount * (long)fnodes[_v].globalNodeCount + (2 - fnodes[_u].fixed - fnodes[_v].fixed), _edgeCount = fnodes[U].edgeCount.get(V);
                if(_u == _v) _smallPi = (_smallPi - fnodes[_v].globalNodeCount) / 2;
                if(U == V) _edgeCount /= 2;

                if(_smallPi - _edgeCount + 1 <= _edgeCount){
                    for(int target: Arrays.asList(_u, _v)){
                        if(fnodes[target].fixed == 1) continue;
                        fnodes[target].fixed = 1;
                        for(long elem: related[target]){
                            int u = (int)(elem >> 31), v = (int)(elem & 0x7FFFFFFFL);
                            if((u != U) || (v != V)) fnodes[u].treeCost.get(v).remove(target);
                            if((u != V) || (v != U)) fnodes[v].treeCost.get(u).remove(target);
                        }
                        IntOpenHashSet newDetermined = new IntOpenHashSet(0);
                        int i = superParent[target];
                        for(int e: fnodes[i].noDecision){
                            long uv = fnodes[i].argVal.get(e);
                            int u = (int)(uv >> 31), v = (int)(uv & 0x7FFFFFFFL);
                            long smallPi = fnodes[u].globalNodeCount * (long)fnodes[v].globalNodeCount, edgeCount = fnodes[i].edgeCount.get(e);
                            int fcnt = (2 - fnodes[u].fixed - fnodes[v].fixed);
                            if(u == v){
                                smallPi = (smallPi - fnodes[v].globalNodeCount) / 2;
                                fcnt /= 2;
                            }
                            if(i == e) edgeCount /= 2;

                            long candidateCost = Long.min(edgeCount, (smallPi + fcnt) - edgeCount + 1), minSuperedgeCost = fnodes[i].edgeCost.get(e), treeCost = fnodes[i].treeCost.get(e).size();
                            long lowerB;
                            if(candidateCost == ((smallPi + fcnt) - edgeCount + 1)){
                                lowerB = candidateCost - fcnt;
                            }else{
                                lowerB = edgeCount;
                            }
                            if(minSuperedgeCost + treeCost <= lowerB){
                                // Slugger
                                determined.enqueue((((((long)i) << 31) + e) << 1) + 0);
                                newDetermined.add(e);
                                cnt_Slugger++;
                            }else if(candidateCost <= minSuperedgeCost){
                                // SWeG
                                determined.enqueue((((((long)i) << 31) + e) << 1) + 1);
                                newDetermined.add(e);
                                cnt_SWeG++;
                            }
                        }
                        for(int e: newDetermined){
                            fnodes[i].noDecision.remove(e);
                            fnodes[e].noDecision.remove(i);
                        }
                    }
                }
            }
        }


        for(int i=0;i<newSupernode;i++){
            if(fnodes[i] != null && fnodes[i].parent == null){
                for(int e: fnodes[i].noDecision){
                    if(i < e) continue;
                    long uv = fnodes[i].argVal.get(e);
                    int u = (int)(uv >> 31), v = (int)(uv & 0x7FFFFFFFL);
                    long smallPi = fnodes[u].globalNodeCount * (long)fnodes[v].globalNodeCount, edgeCount = fnodes[i].edgeCount.get(e);
                    int fcnt = (2 - fnodes[u].fixed - fnodes[v].fixed);
                    if(u == v){
                        smallPi = (smallPi - fnodes[v].globalNodeCount) / 2;
                        fcnt /= 2;
                    }
                    if(i == e) edgeCount /= 2;

                    long candidateCost = Long.min(edgeCount, (smallPi + fcnt) - edgeCount + 1), minSuperedgeCost = fnodes[i].edgeCost.get(e);
                    IntOpenHashSet treeCost = fnodes[i].treeCost.get(e);
                    if(minSuperedgeCost + treeCost.size() <= candidateCost){
                        // Slugger
                        for(int target: treeCost){
                            if(fnodes[target].fixed == 1) continue;
                            fnodes[target].fixed = 1;
                            for(long elem: related[target]){
                                int _u = (int)(elem >> 31), _v = (int)(elem & 0x7FFFFFFFL);
                                if(_u != i || _v != e) fnodes[_u].treeCost.get(_v).remove(target);
                                if(_u != e || _v != i) fnodes[_v].treeCost.get(_u).remove(target);
                            }
                        }
                        fnodes[i].edgeCost.put(e, 0);
                        fnodes[e].edgeCost.put(i, 0);
                        cnt_Slugger++;
                    }else{
                        // SWeG
                        for(int target: Arrays.asList(u, v)){
                            if(fnodes[target].fixed == 1) continue;
                            fnodes[target].fixed = 1;
                            for(long elem: related[target]){
                                int _u = (int)(elem >> 31), _v = (int)(elem & 0x7FFFFFFFL);
                                if(_u != i || _v != e) fnodes[_u].treeCost.get(_v).remove(target);
                                if(_u != e || _v != i) fnodes[_v].treeCost.get(_u).remove(target);
                            }
                        }
                        fnodes[i].edgeCost.put(e, 1);
                        fnodes[e].edgeCost.put(i, 1);
                        cnt_SWeG++;
                    }
                }
            }
        }


        long totalEdgeCnt = 0; long totalSEdgeCnt = 0;
        for(int i=0;i<newSupernode;i++){
            if(fnodes[i] == null || fnodes[i].edges == null) continue;
            int sparent = superParent[i];
            IntOpenHashSet newEdges = new IntOpenHashSet(fnodes[i].edges.size());
            for(int _e: fnodes[i].edges){
                int e = (_e < 0) ? (~_e) : _e;
                int _sparent = superParent[e];

                if(fnodes[sparent].edgeCost.get(_sparent) == 0){
                    newEdges.add(_e);
                    long smallPi = fnodes[i].globalNodeCount * (long)fnodes[e].globalNodeCount;
                    if(i == e) smallPi -= fnodes[i].globalNodeCount;
                    totalEdgeCnt += (_e < 0) ? (-smallPi) : (smallPi);
                }
                totalSEdgeCnt += 1;
            }
            fnodes[i].edges = newEdges;
        }


        int expectedPlus = 0, expectedMinus = 0, realMinus = 0, realPlus = 0;
        int cnt_cases = 0;

        // FOR SWeG-MAPPING
        int scnt = 0;
        for(int i=0;i<newSupernode;i++){
            if(fnodes[i] != null && fnodes[i].parent == null){
                for(Int2IntMap.Entry e: Int2IntMaps.fastIterable(fnodes[i].edgeCost)){
                    if(i < e.getIntKey()) continue;
                    if(e.getIntValue() == 0) continue;
                    scnt += 1;
                    long uv = fnodes[i].argVal.get(e.getIntKey());
                    int u = (int)(uv >> 31), v = (int)(uv & 0x7FFFFFFFL);
                    long smallPi = fnodes[u].globalNodeCount * (long)fnodes[v].globalNodeCount, edgeCount = fnodes[i].edgeCount.get(e.getIntKey());
                    int tCost = (2 - fnodes[u].fixed - fnodes[v].fixed);
                    if(u == v){
                        smallPi = (smallPi - fnodes[v].globalNodeCount) / 2;
                        tCost /= 2;
                    }
                    if(i == e.getIntKey()) edgeCount /= 2;
                    if((smallPi + tCost) - edgeCount + 1 <= edgeCount){
                        expectedMinus += 2 * (int)(smallPi - edgeCount);
                        fnodes[u].edges.add(v);
                        fnodes[v].edges.add(u);
                        totalEdgeCnt += (smallPi + smallPi);
                    }else{
                        expectedPlus += 2 * (int)edgeCount;
                        totalEdgeCnt += 0;
                    }
                }
            }
        }

//         totalEdgeCnt = 0; long totalLoopCnt = 0; totalSEdgeCnt = 0;
//         for(int i=0;i<newSupernode;i++){
//             if(fnodes[i] == null || fnodes[i].edges == null) continue;
//             for(int _e: fnodes[i].edges){
//                 int e = (_e < 0) ? (~_e) : _e;
//                 long smallPi = fnodes[i].globalNodeCount * (long)fnodes[e].globalNodeCount;
//                 if(i == e){
//                     smallPi -= fnodes[i].globalNodeCount;
//                     totalLoopCnt += (_e < 0) ? (-smallPi) : (smallPi);
//                 }else{
//                     totalEdgeCnt += (_e < 0) ? (-smallPi) : (smallPi);
//                 }
//                 if(i == e) totalSEdgeCnt += 1;
//                 totalSEdgeCnt += 1;
//             }
//         }
// //        System.out.println(totalEdgeCnt + " " + totalLoopCnt + " " + totalSEdgeCnt + " " + (totalEdgeCnt + totalLoopCnt + expectedPlus - expectedMinus));

        int finalEdgeCnt = 0;
        int finalTreeCost = 0, finalNodeCounts = 0, finalSupernodeCounts = 0, finalIntermediateNodes = 0, finalIntermeidateCount = 0, finalSingletonSupernodeCounts = 0;


        for(int i=0;i<newSupernode;i++){
            if(fnodes[i] == null) continue;
            if(fnodes[i].children != null) fnodes[i].updateChildren();
        }

        int finalExpectedIntermeidateCount = 0, finalExpectedSupernodeCount = 0;


        int zeroCases = 0, zeroPossibleCase1 = 0, zeroPossibleCase2 = 0;
        for(int i=newSupernode-1;i>=0;i--){
            if(fnodes[i] == null) continue;
            if(fnodes[i].children != null && fnodes[i].edges.size() == 0){
                if(fnodes[i].children != null){
                    for(FinalTree v: fnodes[i].children){
                        zeroCases += 1;
                        if(v.parent == fnodes[i]){
                            if(fnodes[i].parent == null) zeroPossibleCase1 += 1;
                        }else{
                            if(fnodes[i].parent != null) zeroPossibleCase2 += 1;
                        }
                        if(fnodes[i].parent == null){
                            v.parent = null;
                        }
                    }
                }
                fnodes[i] = null;
            }
            if(fnodes[i] != null){
                finalExpectedIntermeidateCount += 1;
                if(fnodes[i].parent == null) finalExpectedSupernodeCount += 1;
            }
        }
        //System.out.println(zeroCases + " " + zeroPossibleCase1 + " " + zeroPossibleCase2);

        for(int i=newSupernode-1;i>=0;i--){
            if(fnodes[i] == null) continue;
            if(fnodes[i].parent == null){
                finalTreeCost += fnodes[i].globalTreeCost;
                finalNodeCounts += fnodes[i].globalNodeCount;
                if(fnodes[i].globalNodeCount == 1) finalSingletonSupernodeCounts += 1;
                finalIntermeidateCount += fnodes[i].totalIntermediateCnt;
                finalSupernodeCounts += 1;
            }
            finalIntermediateNodes += 1;
            if(fnodes[i].edges != null){
                for(int e: fnodes[i].edges){
                    if(i == e || i == (~e)) finalEdgeCnt += 1;
                }
                finalEdgeCnt += fnodes[i].edges.size();
            }
        }

        BufferedWriter h = new BufferedWriter(new FileWriter("summary/H.txt"));
        BufferedWriter Pplus = new BufferedWriter(new FileWriter("summary/Pplus.txt"));
        BufferedWriter Pminus = new BufferedWriter(new FileWriter("summary/Pminus.txt"));


        IntOpenHashSet[] forH = new IntOpenHashSet[newSupernode];
        IntOpenHashSet[] forPp = new IntOpenHashSet[newSupernode];
        IntOpenHashSet[] forPm = new IntOpenHashSet[newSupernode];


        checker = new Int2IntOpenHashMap[n];
        int hOne = 0;
        for(int i=0;i<n;i++){
            checker[i] = new Int2IntOpenHashMap();
            FinalTree node = fnodes[i];
            FinalTree prev;
            ObjectArrayList<FinalTree> stk = new ObjectArrayList<>(1);
            if(node.parent!=null) hOne++;
            while(node != null){
                stk.add(node);
                prev = node;
                node = node.parent;
                if(node!=null){
                    if(forH[prev.num] == null){
                        forH[prev.num] = new IntOpenHashSet();
                    }
                    if(forH[prev.num].contains(node.num)) continue;
                    forH[prev.num].add(node.num);
                }
            }
            while(!stk.isEmpty()){
                if(stk.top().edges != null){
                    for(int e: stk.top().edges){
                        if(e < 0){
                            if(forPm[stk.top().num] == null){
                                forPm[stk.top().num] = new IntOpenHashSet();
                            }
                            forPm[stk.top().num].add((~e));
                            for(int u: ref[~e].nodes){
                                if(i != u) checker[i].addTo(u, -1);
                            }
                        } else {
                            if(forPp[stk.top().num] == null){
                                forPp[stk.top().num] = new IntOpenHashSet();
                            }
                            forPp[stk.top().num].add(e);
                            for(int u: ref[e].nodes){
                                if(i != u) checker[i].addTo(u, 1);
                            }
                        }
                    }
                }
                stk.pop();
            }
            for(int u: adjList[i]){
                if(checker[i].getOrDefault(u, 0) != 1){
                    if(checker[i].getOrDefault(u, 0) == 2){
                        if(forPm[i] == null){
                            forPm[i] = new IntOpenHashSet();
                        }
                        forPm[i].add(u);
                        realMinus++;
                    }
                    else if(checker[i].getOrDefault(u, 0) == 0){
                        if(forPp[i] == null){
                            forPp[i] = new IntOpenHashSet();
                        }
			            forPp[i].add(u);
                        realPlus++;
                    }
                }
                checker[i].remove(u);
            }
            for(Int2IntMap.Entry e: Int2IntMaps.fastIterable(checker[i])){
                if(e.getIntValue() == 1){
                    if(forPm[i] == null){
                        forPm[i] = new IntOpenHashSet();
                    }
                    forPm[i].add(e.getIntKey());
                    realMinus++;
                }
                else if(e.getIntValue() == -1){
                    if(forPp[i] == null){
                        forPp[i] = new IntOpenHashSet();
                    }
                    forPp[i].add(e.getIntKey());
                    realPlus++;
                }
                else if(e.getIntValue() != 0) System.out.println("###");
            }
        }
        System.out.println("compression ratio: " + ((((finalEdgeCnt + expectedPlus + expectedMinus) / 2) + finalTreeCost + hOne) / (double)(_oldEdgeCnt/2)));
        System.out.println("Done! Validation for delta: " + ((expectedPlus == realPlus) && (expectedMinus == realMinus)));

        Int2IntOpenHashMap reverseVmap = new Int2IntOpenHashMap(0);
        for(Int2IntMap.Entry e: Int2IntMaps.fastIterable(vmap)){
            reverseVmap.addTo(e.getIntValue(), e.getIntKey());
        }
        vmap = null;

        for(int i = 0 ; i < newSupernode; i++){
            if(forH[i]!=null){
                for(int x: forH[i]){
                    String src, dst;
                    if(i < x){
                        src = "n" + i;
                        dst = "n" + x;
                        if(i < n){
                            src = Integer.toString(reverseVmap.get(i));
                        }
                        if(x < n){
                            dst = Integer.toString(reverseVmap.get(x));
                        }
                        h.write(src+" "+dst);
                        h.newLine();
                    }
                }
            }
            if(forPp[i]!=null){
                for(int x: forPp[i]){
                    String src, dst;
                    if(i <= x){
                        src = "n"+i;
                        dst = "n"+x;
                        if(i < n){
                            src = Integer.toString(reverseVmap.get(i));
                        }
                        if(x < n){
                            dst = Integer.toString(reverseVmap.get(x));
                        }
                        Pplus.write(src + " " + dst);
                        Pplus.newLine();
                    }
                }
            }
            if(forPm[i]!=null){
                for(int x: forPm[i]){
                    String src, dst;
                    if(i <= x){
                        src = "n"+i;
                        dst = "n"+x;
                        if(i < n){
                            src = Integer.toString(reverseVmap.get(i));
                        }
                        if(x < n){
                            dst = Integer.toString(reverseVmap.get(x));
                        }
                        Pminus.write(src + " " + dst);
                        Pminus.newLine();
                    }
                }
            }
        }
        forH = null;
        forPp = null;
        forPm = null;
        h.close();
        Pminus.close();
        Pplus.close();
    }


    private void dfsBlock(int idx, int cnt, int pos, int neg, int minus, int zero, int plus){
        if(idx == 13){
            for(int i=0;i<256;i++){
                int rev_i = i ^ 255;
                if((i & minus) > 0) continue;
                int resPlus = (i & zero) ^ (rev_i & minus);
                int resMinus = (rev_i & plus);
                int final_cnt = cnt + bitcnt[resPlus ^ resMinus];
                if(final_cnt < cost[i]){
                    bestMaps[i].clear();
                    cost[i] = final_cnt;
                }
                if(final_cnt == cost[i]) bestMaps[i].add( (((long)(pos + (resPlus << 13))) << 21) + ((long)(neg + (resMinus << 13))) );
            }
            return;
        }
        int cap_minus = minus & fullMap[idx], cap_zero = zero & fullMap[idx], cap_plus = plus & fullMap[idx];
        if(cap_minus == 0) dfsBlock(idx+1, cnt+1, pos, neg ^ (1 << idx), minus ^ cap_zero, zero ^ cap_zero ^ cap_plus, plus ^ cap_plus);
        dfsBlock(idx+1, cnt, pos, neg, minus, zero, plus);
        if(cap_plus == 0) dfsBlock(idx+1, cnt+1, pos ^ (1 << idx), neg, minus ^ cap_minus, zero ^ cap_zero ^ cap_minus, plus ^ cap_zero);
    }

    private void dfsSelfBlock(int idx, int cnt, int pos, int neg, int minus, int zero, int plus){
        if(idx == 18){
            for(int i=0;i<1024;i++){
                int rev_i = i ^ 1023;
                if((i & minus) > 0) continue;
                int resPlus = (i & zero) ^ (rev_i & minus);
                int resMinus = (rev_i & plus);
                int final_cnt = cnt + bitcnt[resPlus ^ resMinus];
                if(final_cnt < selfCost[i]){
                    selfBestMaps[i].clear();
                    selfCost[i] = final_cnt;
                }
                if(final_cnt == selfCost[i]) selfBestMaps[i].add( (((long)(pos + (resPlus << 18))) << 28) + ((long)(neg + (resMinus << 18))) );
            }
            return;
        }
        if(idx == 1 || idx == 2 || idx == 6 || idx == 7 || idx == 8 || idx == 9 || idx == 10 || idx == 11 || idx == 16 || idx == 17){
            dfsSelfBlock(idx+1, cnt, pos, neg, minus, zero, plus);
        }else{
            int cap_minus = minus & selfFullMap[idx], cap_zero = zero & selfFullMap[idx], cap_plus = plus & selfFullMap[idx];
            if(cap_minus == 0) dfsSelfBlock(idx+1, cnt+1, pos, neg ^ (1 << idx), minus ^ cap_zero, zero ^ cap_zero ^ cap_plus, plus ^ cap_plus);
            dfsSelfBlock(idx+1, cnt, pos, neg, minus, zero, plus);
            if(cap_plus == 0) dfsSelfBlock(idx+1, cnt+1, pos ^ (1 << idx), neg, minus ^ cap_minus, zero ^ cap_zero ^ cap_minus, plus ^ cap_zero);
        }

    }

    private void buildMap() throws IOException {
        for(int i=0;i<256;i++){
            cost[i] = 13 + 1;
            bestMaps[i] = new LongArrayList(1);
            fours[i] = 0;
        }
        int[] minStates = new int[512];
        for(int i=0;i<512;i++){
            minStates[i] = 0;
            for(int j=0;j<9;j++){
                if((i & (1 << j)) > 0) minStates[i] ^= minMap[j];
            }
        }
        dfsBlock(0, 0, 0, 0, 0, 255, 0);

        File file2 = new File("Map/neigh.txt");
        FileWriter fw = new FileWriter(file2, false);

        for(int i=0;i<256;i++){
            for(long mapping: bestMaps[i]){
                int pos = (int)(mapping >> 21), neg = (int)(mapping & ((long)(1 << 21) - 1));
                int minState = (minStates[(pos & 511)] ^ minStates[(neg & 511)]);
                dropMaps[i][minState] = mapping;
                fours[i] = fours[i] | (1 << minState);
                String _tmp = "";
                boolean first = true;
                for(int k=0;k<21;k++){
                    if((pos & (1 << k)) > 0){
                        _tmp += (first ? "" : ",") + Integer.toString(k);
                        first = false;
                    }
                    if((neg & (1 << k)) > 0){
                        _tmp += (first ? "-" : ",-") + Integer.toString(k);
                        first = false;
                    }
                }
                fw.write(i + ";" + _tmp + ";" + minState + "\n");
            }
            bestMaps[i] = null;
        }
        fw.close();
    }

    private void buildSMap() throws IOException {
        for(int i=0;i<1024;i++){
            selfCost[i] = 18 + 1;
            selfBestMaps[i] = new LongArrayList(1);
            threes[i] = 0;
        }
        int[] minStates = new int[64];
        for(int i=0;i<64;i++){
            minStates[i] = 0;
            for(int j=0;j<9;j++){
                if((i & (1 << j)) > 0) minStates[i] ^= selfMinMap[j];
            }
        }
        dfsSelfBlock(0, 0, 0, 0, 0, 1023, 0);

        File file2 = new File("Map/self.txt");
        FileWriter fw = new FileWriter(file2, false);

        selfloop_mark = new IntArrayList[128];
        for(int i=0;i<128;i++){
            selfloop_mark[i] = new IntArrayList(1);
            selfloop_mark[i].add(0);
            if((i & 64) > 0){
                selfloop_mark[i].add(1023);
                continue;
            }
            if((i & 16) > 0){
                int sz = selfloop_mark[i].size();
                for(int j=0;j<sz;j++) selfloop_mark[i].add(selfloop_mark[i].getInt(j) ^ 7);
            }
            if((i & 32) > 0){
                int sz = selfloop_mark[i].size();
                for(int j=0;j<sz;j++) selfloop_mark[i].add(selfloop_mark[i].getInt(j) ^ 896);
            }
        }

        for(int i=0;i<1024;i++){
            for(long mapping: selfBestMaps[i]){
                int pos = (int)(mapping >> 28), neg = (int)(mapping & ((long)(1 << 28) - 1));
                int selfMinState = (minStates[(pos & 63)] ^ minStates[(neg & 63)]);
                if(selfDropMaps[i][selfMinState] == null) selfDropMaps[i][selfMinState] = new LongArrayList(1);
                selfDropMaps[i][selfMinState].add(mapping);
                threes[i] = threes[i] | (1 << selfMinState);

                String _tmp = "";
                boolean first = true;
                for(int k=0;k<28;k++){
                    if((pos & (1 << k)) > 0){
                        _tmp += (first ? "" : ",") + Integer.toString(k);
                        first = false;
                    }
                    if((neg & (1 << k)) > 0){
                        _tmp += (first ? "-" : ",-") + Integer.toString(k);
                        first = false;
                    }
                }
                fw.write(i + ";" + _tmp + ";" + (minStates[(pos & 63)] ^ minStates[(neg & 63)]) + "\n");
            }
        }
        fw.close();
    }
}