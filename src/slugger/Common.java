package slugger;

import java.io.*;

public class Common {
    public Common(){}

    private static int[] parseEdge(String line, String delim){
        String[] tokens = line.split(delim);
        try {
            int src = Integer.valueOf(tokens[0]);
            int dst = Integer.valueOf(tokens[1]);
            return new int[]{src, dst};
        }catch(Exception e){
            return null;
        }
    }

    public static int runBatch(final SummaryGraphModule module, final boolean isBatch, final String inputPath, final String delim) throws IOException{
        int count = 0;
        long start = System.currentTimeMillis();
        
        BufferedReader br = new BufferedReader(new FileReader(inputPath));
        while(true){
            final String line = br.readLine();
            if(line == null) break;
            final int[] edge = parseEdge(line, delim);
            if(edge == null) break;
            if(edge[0] == edge[1]) continue;
            count += 1;
            module.processAddition(edge[0], edge[1]);
        }
        br.close();
        module.setFlag(true);
        br = new BufferedReader(new FileReader(inputPath));
        while(true){
            final String line = br.readLine();
            if(line == null) break;
            final int[] edge = parseEdge(line, delim);
            if(edge == null) break;
            if(edge[0] == edge[1]) continue;
            count += 1;
            module.processAddition(edge[0], edge[1]);
        }
        module.processBatch();
        br.close();

        long end = System.currentTimeMillis();
        System.out.println("Execution time: " + (end - start) / 1000.0 + "s.");
        return count;
    }
}
