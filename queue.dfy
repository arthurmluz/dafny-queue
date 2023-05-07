class {:autocontracts} CircularQueue
{

    // implementation
    var a    : array<nat>;
    var start: nat;
    var end  : nat;


    //abstraction
    ghost var   list: seq<nat>;
    ghost var   len : nat;

    ghost predicate Valid() {
        start >= 0         &&
        end   >= 0         &&
        end   >= start     &&
        start <= end       &&
        len   >= 0         &&
        len   == end-start &&
        a.Length >= end    &&
        list == a[start..end] &&
        |list| == end-start
    }

    constructor()
        ensures list  == []
        ensures len   == 0
        ensures start == 0
        ensures end   == 0
    {
        a     := new nat[2];
        start := 0;
        end   := 0;

        list := [];
        len  := 0;
    }

    method insert(e: nat)
        ensures list == old(list) + [e]
        ensures end == old(end+1)
        ensures len == old(len) +1
        ensures start == old(start)
        {
            // if our list is out of space, make it bigger
            if end == a.Length
             {
                var b := new nat[end+2];
                // clones our list to b
                forall i | 0 <= i < end
                {
                    b[i] := a[i];
                }
                a := b;
            }
                
            a[end] := e;
            end := end +1;

            list := list + [e];
            len  := len + 1;
        }
   
    method pop() returns (e:nat)
        requires end - start > 0
        ensures start == old(start+1)
        ensures e     == old(list[0])
        ensures end   == old(end)
        ensures list == old(list)[1..]
        {
            e     := a[start];
            start := start +1;
            list := list [1..];
            len  := len -1;
        }

    method has(e:nat) returns (r : bool)
        requires isEmpty() == false
        ensures r == true  ==> exists i :: start <= i < end &&  a[i] == e 
        ensures r == false ==> forall j :: start <= j < end ==> a[j] != e 
        ensures list == old(list)
        ensures start == old(start)
        ensures end == old(end)
        {
            r := false;
            var i := start;
            while i < end 
                invariant start <= i <= end
                invariant forall k :: start <= k < i ==> a[k] != e
                invariant r == true ==> a[i] == e && a[i] in a[start..end]
                decreases end-i
            {
                if a[i] == e {
                    r := true;
                    break;
                }
                i := i + 1;
            }
        }
    
    method count() returns (r: nat)
        ensures r == (end-start)
        ensures r == len
        {
           r := end-start;
        }
        
    function isEmpty(): bool
        ensures isEmpty() == false  ==> end - start > 0
        ensures isEmpty() == true ==> end - start == 0
        {
            end <= start
        }
}

method concat(a : CircularQueue, b : CircularQueue) returns (r : CircularQueue)
    requires a.len > 0
    requires b.len > 0
    requires a.Valid() && b.Valid()
    ensures  a.Valid() && b.Valid()
    ensures fresh(r)
    ensures r.list[..] == a.list[..] + b.list[..]
    ensures r.len == a.len + b.len
    // garanties that original queues didnt change
    ensures a.list == old(a.list) && a.end == old(a.end) && a.start == old(a.start) && a.len == old(a.len)
    ensures b.list == old(b.list) && b.end == old(b.end) && b.start == old(b.start) && b.len == old(b.len)
    {
        r := new CircularQueue();
        assert r.len == 0;
        assert r.start == 0;
        assert r.end == 0;

        var i := a.start;
        while i < a.end
            decreases a.end - i
            invariant a.start <= i <= a.end
            invariant forall k :: 0 <= k < (a.start-i) ==> r.a[k] == a.a[a.start+k]
            invariant a.list == old(a.list) && a.end == old(a.end) && a.start == old(a.start) && a.len == old(a.len) 
            invariant b.list == old(b.list) && b.end == old(b.end) && b.start == old(b.start) && b.len == old(b.len) 
        {
            r.insert(a.a[i]);
            i := i + 1;
        }

        i := b.start;
        while i < b.end
            decreases b.end - i
            invariant b.start <= i <= b.end
            invariant forall k :: r.end <= k < (b.start-i) ==> r.a[k] == b.a[b.start+k]
            invariant a.list == old(a.list) && a.end == old(a.end) && a.start == old(a.start) && a.len == old(a.len) 
            invariant b.list == old(b.list) && b.end == old(b.end) && b.start == old(b.start) && b.len == old(b.len) 
        {
            r.insert(b.a[i]);
            i := i + 1;
        }
        assert r.list == a.list + b.list;
    }

method main(){
    var c := new CircularQueue();
    assert c.list == [];
    c.insert(0);
    assert c.list[..] == [0];
    assert c.a[c.start..c.end] == [0];
    assert c.end == 1;
    assert c.list[c.start] == 0;
    assert c.len == 1;

    c.insert(2);
    assert c.list[..] == [0,2];
    assert c.a[c.start..c.end] == [0,2];
    assert c.end == 2;
    assert c.len == 2;

    c.insert(3);
    assert c.list[..] == [0,2,3];
    assert c.a[c.start..c.end] == [0,2,3];
    assert c.end == 3;
    assert c.start == 0;
    assert c.len == 3;

    var e := c.pop();
    assert e == 0;
    assert c.len == 2;
    assert c.end == 3;
    assert c.start == 1;
    assert c.a[c.start..c.end] == [2,3];
    assert c.list[..] == [2,3];

    var vazia := c.isEmpty();
    assert c.start == 1;
    assert c.end == 3;
    assert vazia == false;

    e := c.pop();
    assert e == 2;
    assert c.end == 3;
    assert c.start == 2;
    assert c.a[c.start] == 3;
    assert c.a[c.start..c.end] == [3];
    assert c.list[..] == [3];

    e := c.pop();
    assert e == 3;
    assert c.end == 3;
    assert c.start == 3;
    assert c.a[c.start..c.end] == [];
    assert c.list[..] == [];

    vazia := c.isEmpty();
    assert vazia == true;

    c.insert(0);
    c.insert(2);
    c.insert(3);
    c.insert(4);
    c.insert(9);
    assert c.start == 3;
    assert c.end == 8;
    assert c.a[c.start..c.end] == [0,2,3,4,9];
    assert c.list[..] == [0,2,3,4,9];

    var f := c.has(3);
    assert c.start == 3;
    assert c.a[5] == 3;
    assert c.end == 8;

    assert f == true;

    f := c.has(213);
    assert f == false;

    var qtd := c.count();
    assert qtd == 5;

    c.insert(213);
    qtd := c.count();
    assert qtd == 6;

    e := c.pop();
    qtd := c.count();
    assert qtd == 5;
}