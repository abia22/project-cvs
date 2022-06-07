package task2;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import task1.CounterSequence;

/*@
    predicate_ctor CounterSeq_shared_state (CCSeq c) () =
    c.capacity() |-> ?cap &*& cap > 0 &*& c.length() |-> ?l &*& l > 0 &*& l <= cap; <- tem que ter as condicoes todas do CounterSeqInv mas nao sei como aceder ao counters.length

    predicate_ctor CounterSeq_nonzero (CCSeq c) () =
    c.capacity() |-> ?cap &*& c.length() |-> ?l &*& cap > 0 &*& l > 0 &*&  l <= cap;

    predicate_ctor CounterSeq_noncap (CCSeq c) () =
    c.capacity() |-> ?cap &*& c.length() |-> ?l &*& l <= cap &*& cap > 0 &*& l >= 0;

    predicate CCSeqInv(CCSeq c;) = 
            c.mon |-> ?l
        &*& l != null
        &*& lck(l,1, CounterSeq_shared_state(c))
        &*& c.notzero |-> ?cn
        &*& cn !=null
        &*& cond(cc, CounterSeq_shared_state(c), CounterSeq_nonzero(c))
        &*& c.notcap |-> ?cc
        &*& cc !=null
        &*& cond(cm, CounterSeq_shared_state(c), CounterSeq_noncap(c));
 *@/

/**
 * Represents a concurrent sequence of Counter objects.
 */
public class CCSeq
{

    private CounterSequence seq;
    ReentrantLock mon;
    Condition notzero;
    Condition notcap;
    
    public CCSeq(int cap)
    //@ requires cap > 0
    //@ ensures CCSeqInv(this)
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
        if(i >= 0 && i < seq.length())
            //@ close CounterSeq_shared_state(this)();
            result = seq.getCounter(i);
        else 
            result = -1;
        mon.unlock();
        return result;
        //@ close [f]CCSeqInv(this);
    }

    public void incr(int i, int val)
    {
        seq.increment(i, val);
    }

    public void decr(int i, int val)
    {
        seq.decrement(i, val);
    }

    public int addCounter(int limit)
    {
        return seq.addCounter(limit);
    }

    public void remCounter(int i)
    {
        seq.remCounter(i);
    }
    
}
