package task2.client;

import task2.*;

import task2.client.*;

/*@
predicate AddSetCountersInv(AddSetCounters t;) = t.counters |-> ?cc &*& cc != null &*& [_]CCSeqInv(cc);
@*/

public class AddSetCounters implements Runnable
{
    //@ predicate pre() = AddSetCountersInv(this);
    //@ predicate post() = AddSetCountersInv(this);

    public static final int NUM_COUNTERS = 50;
    public static final int NUM_OPS = 10;
    public static final int LIMIT = 9999;

    private final CCSeq counters;

    /**
     * @param counters
     */
    public AddSetCounters(CCSeq counters)
    //@ requires counters != null &*& [?f] CCSeqInv(counters);
    //@ ensures AddSetCountersInv(this);
    {
        this.counters = counters;
    }

    public void run()
    //@ requires pre();
    //@ ensures post();
    {

        int counter;

        for (int i = 0; i < NUM_COUNTERS; i++)
        //@ invariant AddSetCountersInv(this);
        {
            counter = counters.addCounter(LIMIT);

            for (int j = 0; j < NUM_OPS / 2; j++)
            //@ invariant AddSetCountersInv(this);
            {
                counters.incr(counter, counter + 10 + j);
            }

            for (int j = 0; j < NUM_OPS / 2; j++)
            //@ invariant AddSetCountersInv(this);
            {
                counters.decr(counter, counter + 5 + j);
            }
        }
    }
}
