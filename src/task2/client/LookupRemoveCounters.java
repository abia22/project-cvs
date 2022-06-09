package task2.client;

import task2.*;

import task2.client.*;

/*@
predicate LookupRemoveCountersInv(LookupRemoveCounters t) = t.counters |-> ?cc &*& cc != null &*& CCSeqInv(cc);
@*/

public class LookupRemoveCounters implements Runnable
{
    public static final int NUM_COUNTERS = 50;

    private final CCSeq counters;

    /**
     * @param counters
     */
    public LookupRemoveCounters(CCSeq counters)
    //@ requires counters != null &*& [?f] CCSeqInv(counters);
    //@ ensures [f] LookupRemoveCountersInv(this);
    {
        this.counters = counters;
    }

    public void run()
    //@ requires pre();
    //@ ensures post();
    {
        for (int counter = 0; counter < NUM_COUNTERS; counter++)
        {
            int value = counters.getCounter(counter);

            if (value >= 0)
            {
                System.out.printf("counter: %d, value: %d\n", counter, value);
                counters.remCounter(counter);
            }
            else
            {
                System.out.printf("Invalid counter: %d\n", counter);
            }
        }
    }
}
