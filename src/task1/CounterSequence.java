package task1;

/*@
predicate CounterP(unit a,Counter c; unit b) = c != null &*& CounterInv(c, ?v, ?lim, ?over) &*& b == unit;

predicate Positive(unit a, int v; unit n) = v > 0 &*& n == unit;

predicate CounterSeqInv(CounterSequence s; int l, int c) =
       	s.capacity |-> c &*& s.length |-> l
        &*& c > 0
        &*& s.sequence |-> ?counters
        &*& counters.length == c
        &*& l >= 0 &*& c >= l
        &*& array_slice_deep(counters, 0, l, CounterP, unit, _, _)
        &*& array_slice(counters, l, c,?rest);
@*/

/**
 * Represents a sequence of Counter objects.
 */
public class CounterSequence
{
    private final Counter[] sequence;
    private int length;
    private final int capacity;

    
    /**
     * Create a sequence of Counter objects with the specified capacity.
     * @param cap The capacity of the sequence of Counters: must be positive.
     */
    public CounterSequence(int cap)
    //@ requires cap > 0;
    //@ ensures CounterSeqInv(this, 0, cap);
    {
        this.sequence = new Counter[cap];
        this.length = 0;
        this.capacity = cap;
    }

    /**
     * Create a sequence that will have as many counters as there are integers in the array
     * (i.e., the capacity of the sequence is the length of the array).
     * 
     * @param arr Each integer in the array denotes the upper-limit of the corresponding counter in sequence.
     */
    public CounterSequence(int[] arr)
    //@ requires arr != null &*& arr.length > 0 &*& array_slice_deep(arr, 0, arr.length, Positive, unit, _, _);
    //@ ensures CounterSeqInv(this, arr.length, arr.length);
    {
        this.sequence = new Counter[arr.length];
        this.length = 0;
        this.capacity = arr.length;

        for (int i = 0; i < arr.length; i++)
        //@ invariant i >= 0 &*& i <= arr.length &*& CounterSeqInv(this, i, arr.length) &*& array_slice_deep(arr, 0, arr.length, Positive, unit, _, _);
        {
            addCounter(arr[i]);
        }
    }

    /**
     * Get the current number of counters.
     * @return the current number of counters.
     */
    public int length()
    //@ requires CounterSeqInv(this, ?l, ?c);
    //@ ensures CounterSeqInv(this, l, c) &*& result == l;
    {
        return this.length;
    }

    /**
     * Get the capacity of the sequence.
     * @return the capacity of the sequence.
     */
    public int capacity()
    //@ requires CounterSeqInv(this, ?l, ?c);
    //@ ensures CounterSeqInv(this, l, c) &*& result == c;
    {
        return this.capacity;
    }

    /**
     * Get the value of the counter is position i of the sequence.
     * 
     * @param i The position of the counter in the sequence: must be between 0 and {@link #length()} (exclusive).
     * 
     * @return the value of the counter is position i of the sequence.
     */
    public int getCounter(int i)
    //@ requires CounterSeqInv(this, ?l, ?c) &*& i >= 0 &*& i < l;
    //@ ensures CounterSeqInv(this, l, c) &*& result >= 0;
    {
        Counter counter = this.sequence[i];
        //@ open CounterInv(counter, ?value, ?lim, ?over);
        
        int result = counter.getVal();
        return result;
    }

    /**
     * Appends a new counter to the end of the sequence with upper-limit given by the parameter limit,
     * assuming the sequence is not at maximum capacity.
     * New counters always start with value 0.
     * 
     * @param limit The limit of the new counter: must be positive.
     * @return the index of the added counter.
     */
    public int addCounter(int limit)
    //@ requires CounterSeqInv(this, ?l, ?c) &*& limit > 0 &*& l < c;
    //@ ensures CounterSeqInv(this, l + 1, c) &*& result == l;
    {
        this.sequence[this.length] = new Counter(0, limit);

        return this.length++;
    }

    /**
     * Remove the counter at the given index of the sequence.
     * This method is not order preserving because it moves the last element of
     * the sequence to the position of the removed counter.
     * 
     * @param pos The position of the counter in the sequence to remove: must be between 0 and {@link #length()} (exclusive).
     */
    public void remCounter(int pos)
    //@ requires CounterSeqInv(this, ?l, ?c) &*& pos >= 0 &*& pos < l;
    //@ ensures CounterSeqInv(this, l - 1, c);
    {
    	if (length - pos > 1)
            this.sequence[pos] = this.sequence[--this.length];
        else
            this.length--;
            
        this.sequence[this.length] = null;
    }

    /**
     * Remove the counter at the given index of the sequence.
     * This method preserves the order of the sequence
     * since it moves all appropriate counters accordingly.
     * 
     * @param pos The position of the counter in the sequence to remove: must be between 0 and {@link #length()} (exclusive).
     */
    public void remCounterPO(int pos)
    //@ requires CounterSeqInv(this, ?l, ?c) &*& pos >= 0 &*& pos < l;
    //@ ensures CounterSeqInv(this, l - 1, c);
    {
        int length = length();
        this.sequence[pos] = null;
        
        for (int i = pos + 1; i < length; i++)
        /*@
            invariant i >= pos + 1 &*& i <= l &*& sequence |-> ?counters
            &*& counters.length == c
            &*& array_element(counters, i - 1, null)
            &*& array_slice_deep(counters, 0, i - 1, CounterP, unit, _, _)
            &*& array_slice_deep(counters, i, l, CounterP, unit, _, _)
            &*& array_slice(counters, l, c,?rest);
        @*/
        {
            this.sequence[i - 1] = this.sequence[i];
            this.sequence[i] = null;
        }
        
        this.sequence[--this.length] = null;
    }

    /**
     * Increment the value of the counter by val in the given position of the sequence.
     * 
     * @param i The position of the counter in the sequence: must be between 0 and {@link #length()} (exclusive).
     * @param val The value to increment: must be positive.
     */
    public void increment(int i, int val)
    //@ requires CounterSeqInv(this, ?l, ?c) &*& i >= 0 &*& i < l &*& val > 0;
    //@ ensures CounterSeqInv(this, l, c);
    {
        this.sequence[i].incr(val);
    }

    /**
     * Decrement the value of the counter by val in the given position of the sequence.
     * 
     * @param i The position of the counter in the sequence: must be between 0 and {@link #length()} (exclusive).
     * @param val The value to decrement: must be positive.
     */
    public void decrement(int i, int val)
    //@ requires CounterSeqInv(this, ?l, ?c) &*& i >= 0 &*& i < l &*& val > 0;
    //@ ensures CounterSeqInv(this, l, c);
    {
        this.sequence[i].decr(val);
    }
}