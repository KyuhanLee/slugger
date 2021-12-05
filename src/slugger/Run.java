package slugger;

import slugger.algorithm.*;

import java.io.*;
import java.util.Date;

public class Run {

    private static SummaryGraphModule module;

    public static void main(String[] args) throws IOException {
        Date today = new Date();
        System.out.println(today);
        final String inputPath = args[0];
        System.out.println("input_path: " + inputPath);
        final boolean optimize = Boolean.parseBoolean(args[1]);


        boolean isBatch = false;
        if(optimize){
            module = new SluggerOpt(false);
        }else{
            module = new Slugger(false);
        }

        Common.runBatch(module, isBatch, inputPath, "\t");
        }
}
