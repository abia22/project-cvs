package task2.client;

import task2.*;

/*@
    predicate pre() = true;
    
    predicate post() = true;
@*/

public class Main
{
    private static final int NUM_THREADS = 100;
    private static final int SEQUENCE_CAPACITY = NUM_THREADS * AddSetCounters.NUM_COUNTERS;

    public static void main(String[] args)
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true; 
    {
        CCSeq counters = new CCSeq(SEQUENCE_CAPACITY);

        for (int i = 0; i < NUM_THREADS; i++)
        //@ invariant [?f] CCSeqInv(counters);
        {
            //@ close [f/2] CCSeqInv(counters);
            new Thread(new AddSetCounters(counters)).start();

            //@ close [f/4] CCSeqInv(counters);
            new Thread(new LookupRemoveCounters(counters)).start();
        }
    }
}
