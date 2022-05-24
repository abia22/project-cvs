package Task1;

public class Counter {

    private int val;
    private int limit;
    private boolean overflow;

    /*@
    predicate CounterInv(int v, int lim, boolean over) = this.val |-> v &*& this.limit |-> lim &*& this.overflow |-> over &*& 0 <= v &*& v < lim;
    @*/

    public Counter(int val, int limit)
    //@ requires 0 <= val &*& val < limit &*& limit > 0;
    //@ ensures CounterInv(val, limit, false);
    {
        this.val = val;
        this.limit = limit;
        this.overflow = false;
    }

    public int getVal()
    //@ requires CounterInv(?value, ?lim, ?over);
    //@ ensures CounterInv(value, lim, over) &*& result == value;
    { 
        return val; 
    }

    public int getLimit()
    //@ requires CounterInv(?value, ?lim, ?over);
    //@ ensures CounterInv(value, lim, over) &*& result == lim;
    { 
        return limit; 
    }

    public void incr(int v)
    //@ requires CounterInv(?value, ?lim, ?over) &*& v >= 0;
    //@ ensures ((value + v) >= lim) ? (CounterInv((value + v) % lim, lim, true)) : CounterInv(value + v, lim, over);
    { 
        if(val + v >= limit){
            val = (val + v) % limit;  
            overflow = true;
        } else
            val = val + v;
     }
    
    public void decr(int v)
    //@ requires CounterInv(?value, ?lim, ?over) &*& v >= 0;
    //@ ensures (value - v < 0) ? (CounterInv(0, lim, true)) : CounterInv(value - v, lim, over); 
    { 
        if(val - v < 0) {
            val = 0;
            overflow = true;
        } else
            val = val - v;
     }
}