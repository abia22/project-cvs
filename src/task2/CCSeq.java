package task2;

import java.util.concurrent.*;
import java.util.concurrent.locks.*;

import task1.*;

/*@
    predicate_ctor CounterSeq_shared_state (CCSeq ccSeq) () =
    ccSeq.seq |-> ?seq &*& seq != null &*& CounterSeqInv(seq, ?l, ?c);

    predicate_ctor CounterSeq_nonzero (CCSeq ccSeq) () =
    ccSeq.seq |-> ?seq &*& seq != null &*& CounterSeqInv(seq, ?l, ?c) &*& l > 0;

    predicate_ctor CounterSeq_noncap (CCSeq ccSeq) () =
    ccSeq.seq |-> ?seq &*& seq != null &*& CounterSeqInv(seq, ?l, ?c) &*& l < c;

    predicate CCSeqInv(CCSeq c;) = 
            c.mon |-> ?l
        &*& l != null
        &*& lck(l,1, CounterSeq_shared_state(c))
        &*& c.notzero |-> ?cn
        &*& cn !=null
        &*& c.notcap |-> ?cc
        &*& cc !=null
        &*& cond(cn, CounterSeq_shared_state(c), CounterSeq_nonzero(c))
        &*& cond(cc, CounterSeq_shared_state(c), CounterSeq_noncap(c));
 @*/

/**
 * Represents a concurrent sequence of Counter objects.
 */
public class CCSeq
{
    private final CounterSequence seq;

    private final ReentrantLock mon;
    private final Condition notzero, notcap;
    
    /**
     * Create a concurrent sequence of Counter objects with the specified capacity.
     * @param cap The capacity of the sequence of Counters: must be positive.
     */
    public CCSeq(int cap)
    //@ requires cap > 0;
    //@ ensures CCSeqInv(this);
    {
        seq = new CounterSequence(cap);
        //@ close CounterSeq_shared_state(this)();
        //@ close enter_lck(1,CounterSeq_shared_state(this));
        mon = new ReentrantLock();
        //@ close set_cond(CounterSeq_shared_state(this),CounterSeq_nonzero(this));
        notzero = mon.newCondition();
        //@ close set_cond(CounterSeq_shared_state(this),CounterSeq_noncap(this));
        notcap = mon.newCondition();
        //@ close CCSeqInv(this);
    }

    /**
     * Get the value of the counter is position i of the sequence.
     * If i is out of bounds then -1 is returned.
     * 
     * @param i The position of the counter in the sequence: must be non negative.
     * 
     * @return the value of the counter is position i of the sequence or -1 if the position is invalid.
     */
    public int getCounter(int i)
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        //@ open [f]CCSeqInv(this);
        int result;
        mon.lock();

        //@ open CounterSeq_shared_state(this)();
        //@ open CounterSeqInv(seq, ?l, ?c);
	    int length = seq.length();

        if(i >= 0 && i < length)
            result = seq.getCounter(i);
        else
            result = -1;

        //@ close CounterSeq_shared_state(this)();
            
        mon.unlock();
        return result;
        //@ close [f]CCSeqInv(this);
    }

    /**
     * Increment the value of the counter by val in the given position of the sequence.
     * 
     * @param i The position of the counter in the sequence: must be non negative.
     * @param val The value to increment: must be positive.
     */
    public void incr(int i, int val)
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        //@ open [f]CCSeqInv(this);
        mon.lock();

        //@ open CounterSeq_shared_state(this)();
        //@ open CounterSeqInv(seq, ?l, ?c);
	    int length = seq.length();

        if(i >= 0 && i < length && val > 0)
            seq.increment(i, val);

        //@ close CounterSeq_shared_state(this)();
            
        mon.unlock();
        //@ close [f]CCSeqInv(this);
    }

    /**
     * Decrement the value of the counter by val in the given position of the sequence.
     * 
     * @param i The position of the counter in the sequence: must be non negative.
     * @param val The value to decrement: must be positive.
     */
    public void decr(int i, int val)
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        //@ open [f]CCSeqInv(this);
        mon.lock();

        //@ open CounterSeq_shared_state(this)();
        //@ open CounterSeqInv(seq, ?l, ?c);
	    int length = seq.length();

        if(i >= 0 && i < length && val > 0)
            seq.decrement(i, val);

        //@ close CounterSeq_shared_state(this)();
            
        mon.unlock();
        //@ close [f]CCSeqInv(this);
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
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        if (limit <= 0)
            return -1;

        //@ open [f]CCSeqInv(this);
        mon.lock();

        //@ open CounterSeq_shared_state(this)();

        while (seq.length() >= seq.capacity())
        /*@ invariant this.seq |-> ?sequence &*& sequence != null
        &*& CounterSeqInv(sequence, ?len, ?cap)
        &*& [f]this.notzero |-> ?cn
        &*& cn !=null
        &*& [f]this.notcap |-> ?cc
        &*& cc !=null
        &*& [f]cond(cn, CounterSeq_shared_state(this), CounterSeq_nonzero(this))
        &*& [f]cond(cc, CounterSeq_shared_state(this), CounterSeq_noncap(this));
        @*/
        {
            //@ close CounterSeq_shared_state(this)();
            try { notcap.await(); } catch (InterruptedException e) {}

            //@ open CounterSeq_noncap(this)();
        }

        //@ open CounterSeqInv(seq, len, cap);
        int pos = seq.addCounter(limit);
        //@ close CounterSeqInv(seq, len + 1, cap);

        //@ close CounterSeq_nonzero(this)();
        
        notzero.signal();
        mon.unlock();
        //@ close [f]CCSeqInv(this);

        return pos;
    }

    /**
     * Remove the counter at the given index of the sequence.
     * This method is not order preserving because it moves the last element of
     * the sequence to the position of the removed counter.
     * 
     * If pos is invalid then no counter is removed.
     * 
     * @param pos The position of the counter in the sequence to remove.
     */
    public void remCounter(int i)
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        if (i < 0)
            return;

        //@ open [f]CCSeqInv(this);
        mon.lock();

        //@ open CounterSeq_shared_state(this)();

        while (seq.length() <= 0)
        /*@ invariant this.seq |-> ?sequence &*& sequence != null
        &*& CounterSeqInv(sequence, ?len, ?cap)
        &*& [f]this.notzero |-> ?cn
        &*& cn !=null
        &*& [f]this.notcap |-> ?cc
        &*& cc !=null
        &*& [f]cond(cn, CounterSeq_shared_state(this), CounterSeq_nonzero(this))
        &*& [f]cond(cc, CounterSeq_shared_state(this), CounterSeq_noncap(this));
        @*/
        {
            //@ close CounterSeq_shared_state(this)();
            try { notzero.await(); } catch (InterruptedException e) {}

            //@ open CounterSeq_nonzero(this)();
        }

        //@ open CounterSeqInv(seq, len, cap);
        if (i < seq.length())
        {
            seq.remCounter(i);
            //@ close CounterSeqInv(seq, len - 1, cap);

            //@ close CounterSeq_noncap(this)();
            notcap.signal();

            //@ open CounterSeq_shared_state(this)();
        }
        //@ close CounterSeq_shared_state(this)();

        mon.unlock();
        //@ close [f]CCSeqInv(this);
    }
}
