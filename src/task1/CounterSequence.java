package task1;

/**
 * Represents a sequence of Counter objects.
 */
public class CounterSequence
{
    private Counter[] sequence;
    private int length;


    /**
     * Create a sequence of Counter objects with the specified capacity.
     * @param cap The capacity of the sequence of Counters: must be non negative.
     */
    public CounterSequence(int cap)
    {
        this.sequence = new Counter[cap];
        this.length = 0;
    }

    /**
     * Create a sequence that will have as many counters as there are integers in the array
     * (i.e., the capacity of the sequence is the length of the array).
     * 
     * @param arr Each integer in the array denotes the upper-limit of the corresponding counter in sequence.
     */
    public CounterSequence(int[] arr)
    {
        this(arr.length);

        for (int limit : arr)
            addCounter(limit);
    }

    /**
     * Get the current number of counters.
     * @return the current number of counters.
     */
    public int length()
    {
        return this.length;
    }

    /**
     * Get the capacity of the sequence.
     * @return the capacity of the sequence.
     */
    public int capacity()
    {
        return this.sequence.length;
    }

    /**
     * Get the value of the counter is position i of the sequence.
     * 
     * @param i The position of the counter in the sequence: must be between 0 and {@link #length()} (exclusive).
     * 
     * @return the value of the counter is position i of the sequence.
     */
    public int getCounter(int i)
    {
        return this.sequence[i].getVal();
    }

    /**
     * Appends a new counter to the end of the sequence with upper-limit given by the parameter limit,
     * assuming the sequence is not at maximum capacity.
     * New counters always start with value 0.
     * 
     * @param limit The limit of the new counter: must be greater than 0.
     * @return the index of the added counter.
     */
    public int addCounter(int limit)
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
    {
        this.sequence[pos] = this.sequence[--this.length];
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
    {
        for (int i = pos + 1; i < this.length; i++)
            this.sequence[i - 1] = this.sequence[i];

        this.sequence[--this.length] = null;
    }

    /**
     * Increment the value of the counter by val in the given position of the sequence.
     * 
     * @param i The position of the counter in the sequence: must be between 0 and {@link #length()} (exclusive).
     * @param val The value to increment: must be non negative.
     */
    public void increment(int i, int val)
    {
        this.sequence[i].incr(val);
    }

    /**
     * Decrement the value of the counter by val in the given position of the sequence.
     * 
     * @param i The position of the counter in the sequence: must be between 0 and {@link #length()} (exclusive).
     * @param val The value to decrement: must be non negative.
     */
    public void decrement(int i, int val)
    {
        this.sequence[i].decr(val);
    }
}