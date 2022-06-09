package task2.client;

import task2.*;

import task2.client.*;

/*@
predicate LookupRemoveCountersInv(LookupRemoveCounters t;) = t.counters |-> ?cc &*& cc != null &*& [_]CCSeqInv(cc);
@*/

public class LookupRemoveCounters implements Runnable
{
    //@ predicate pre() = LookupRemoveCountersInv(this) &*& [_]System_out(?o) &*& o != null;
    //@ predicate post() = LookupRemoveCountersInv(this);

    public static final int NUM_COUNTERS = 50;

    private final CCSeq counters;

    /**
     * @param counters
     */
    public LookupRemoveCounters(CCSeq counters)
    //@ requires counters != null &*& [?f] CCSeqInv(counters);
    //@ ensures LookupRemoveCountersInv(this);
    {
        this.counters = counters;
    }

    public void run()
    //@ requires pre();
    //@ ensures post();
    {
        for (int counter = 0; counter < NUM_COUNTERS; counter++)
        //@ invariant LookupRemoveCountersInv(this) &*& [_]System_out(?o) &*& o != null;
        {
            int value = counters.getCounter(counter);

            if (value >= 0)
            {
                System.out.println("counter: " + String.valueOf(counter) + ", value: " + String.valueOf(value));
                counters.remCounter(counter);
            }
            else
            {
                System.out.println("Invalid counter: " + String.valueOf(counter));
            }
        }
    }
}
