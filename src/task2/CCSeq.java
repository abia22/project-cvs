package task2;

import java.util.concurrent.*;
import java.util.concurrent.locks.*;

//import java.util.concurrent.locks.Condition;
//import java.util.concurrent.locks.ReentrantLock;

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

    public void incr(int i, int val)
    //@ requires [?f]CCSeqInv(this) &*& val > 0;
    //@ ensures [f]CCSeqInv(this);
    {
        //@ open [f]CCSeqInv(this);
        mon.lock();

        //@ open CounterSeq_shared_state(this)();
        //@ open CounterSeqInv(seq, ?l, ?c);
	    int length = seq.length();

        if(i >= 0 && i < length)
            seq.increment(i, val);

        //@ close CounterSeq_shared_state(this)();
            
        mon.unlock();
        //@ close [f]CCSeqInv(this);
    }

    public void decr(int i, int val)
    //@ requires [?f]CCSeqInv(this) &*& val > 0;
    //@ ensures [f]CCSeqInv(this);
    {
        //@ open [f]CCSeqInv(this);
        mon.lock();

        //@ open CounterSeq_shared_state(this)();
        //@ open CounterSeqInv(seq, ?l, ?c);
	    int length = seq.length();

        if(i >= 0 && i < length)
            seq.decrement(i, val);

        //@ close CounterSeq_shared_state(this)();
            
        mon.unlock();
        //@ close [f]CCSeqInv(this);
    }

    public int addCounter(int limit)
    //@ requires [?f]CCSeqInv(this) &*& limit > 0;
    //@ ensures [f]CCSeqInv(this);
    {
        //@ open [f]CCSeqInv(this);
        mon.lock();

        //@ open CounterSeq_shared_state(this)();

        while (seq.length() >= seq.capacity())
        /*@ invariant this.seq |-> ?sequence &*& sequence != null &*& CounterSeqInv(sequence, ?len, ?cap) &*& [f]this.notzero |-> ?cn
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

    /* public void remCounter(int i)
    {
        seq.remCounter(i);
    } */
    
}
