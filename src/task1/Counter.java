package task1;

/*@
    predicate CounterInv(Counter c; int v, int lim, boolean over) = c.val |-> v &*& c.limit |-> lim &*& c.overflow |-> over &*& 0 <= v &*& v < lim &*& lim > 0;
@*/

/**
 * A sequential counter.
 */
public class Counter {

    private int val;
    private int limit;
    private boolean overflow;

    /**
     * Create a counter with the specified initial value and limit.
     * 
     * @param val Initial value: non negative and less than limit.
     * @param limit The limit: greater than 0.
     */
    public Counter(int val, int limit)
    //@ requires 0 <= val &*& val < limit &*& limit > 0;
    //@ ensures CounterInv(this, val, limit, false);
    {
        this.val = val;
        this.limit = limit;
        this.overflow = false;
    }

    /**
     * Get the current value of the counter.
     * @return the current value of the counter.
     */
    public int getVal()
    //@ requires CounterInv(this, ?value, ?lim, ?over);
    //@ ensures CounterInv(this, value, lim, over) &*& result == value;
    { 
        return val; 
    }

    /**
     * Get the limit of the counter.
     * @return the limit of the counter.
     */
    public int getLimit()
    //@ requires CounterInv(this, ?value, ?lim, ?over);
    //@ ensures CounterInv(this, value, lim, over) &*& result == lim;
    { 
        return limit; 
    }

    /**
     * Increment the counter by v.
     * If the final result is greater than or equal to {@link #getLimit()} then overflow is true
     * and the result is set to ( old( {@link #getVal()} ) + v ) % {@link #getLimit()}.
     * @param v The value to increment: must be non negative.
     */
    public void incr(int v)
    //@ requires CounterInv(this, ?value, ?lim, ?over) &*& v >= 0;
    //@ ensures ((value + v) >= lim) ? (CounterInv(this, (value + v) % lim, lim, true)) : CounterInv(this, value + v, lim, over);
    { 
        if(val + v >= limit){
            val = (val + v) % limit;  
            overflow = true;
        } else
            val = val + v;
     }
    
     /**
     * Decrement the counter by v.
     * If the final result is negative then overflow is true and the result is set to 0.
     * @param v The value to decrement.: must be non negative.
     */
    public void decr(int v)
    //@ requires CounterInv(this, ?value, ?lim, ?over) &*& v >= 0;
    //@ ensures (value - v < 0) ? (CounterInv(this, 0, lim, true)) : CounterInv(this, value - v, lim, over); 
    { 
        if(val - v < 0) {
            val = 0;
            overflow = true;
        } else
            val = val - v;
     }
}