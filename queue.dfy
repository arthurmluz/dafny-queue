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
        start >= 0       &&
        start <= len     &&
        end   >= 0       &&
        end   >= start   &&
        len   >= 0       &&
        len   >= end     &&
        a.Length == len &&
        list == a[0..end]
    }

    constructor()
        ensures list == []
        ensures start == 0
        ensures end == 0
    {
        a     := new nat[2];
        start := 0;
        end   := 0;

        list := [];
        len  := 2;
    }

    method insert(e: nat)
        ensures list == old(list) + [e]
        ensures end == old(end+1)
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
                len := end+2;
            }
                
            a[end] := e;
            end := end +1;

            list := list + [e];
        }


   
    method pop() returns (e:nat)
        requires end - start > 0
        ensures start == old(start+1)
        ensures e     == list[old(start)]
        ensures end   == old(end)
        ensures list == old(list)
        {
            e     := a[start];
            start := start +1;
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

        
    function isEmpty(): bool
        ensures isEmpty() == false  ==> end - start > 0
        ensures isEmpty() == true ==> end - start == 0
        {
            end <= start
        }


    // method concat(queue : CircularQueue) returns (r : CircularQueue)
    //     requires queue.end - queue.start > 0
    //     ensures r.list[..] == (list[..] + queue.list[..])
    //     ensures r.end == end + (queue.end - queue.end)
    //     // garanties that this queue didnt change
    //     ensures list == old(list) && end == old(end) && start == old(start)
    //     ensures queue.list == old(queue.list) && queue.end == old(queue.end) && queue.start == old(queue.start)
    //     {
    //         r := new CircularQueue();
    //         var i := start;
    //         var j := 0;
    //         while i < end
    //             invariant start <= i <= end
    //             decreases end-i
    //         {
    //             r.insert(a[i]);
    //             i := i + 1;
    //             j := j + 1;
    //         }

    //         assert r.list == a[start..end];
    //         i := queue.start;
    //         // while i < queue.end
    //             // invariant queue.start <= i <= queue.end
    //         // {
    //             // r.insert(queue.a[i]);
    //         // }
    //     }
}

method main(){
    var c := new CircularQueue();
    assert c.list == [];
    c.insert(0);
    assert c.list[c.start..c.end] == [0];
    assert c.end == 1;
    assert c.list[c.start] == 0;
    c.insert(2);
    assert c.list[c.start..c.end] == [0,2];
    assert c.end == 2;
    c.insert(3);
    assert c.list[c.start..c.end] == [0,2,3];
    assert c.end == 3;
    assert c.start == 0;
    assert c.list[c.start] == 0;
    var e := c.pop();
    assert e == 0;
    assert c.end == 3;
    assert c.start == 1;
    assert c.list[c.start] == 2;
    assert c.list[c.start..c.end] == [2,3];

    var vazia := c.isEmpty();
    assert c.start == 1;
    assert c.end == 3;
    assert vazia == false;

    e := c.pop();
    assert e == 2;
    assert c.end == 3;
    assert c.start == 2;
    assert c.list[c.start] == 3;
    assert c.list[c.start..c.end] == [3];

    e := c.pop();
    assert e == 3;
    assert c.end == 3;
    assert c.start == 3;
    assert c.list[c.start..c.end] == [];

    vazia := c.isEmpty();
    assert vazia == true;

    c.insert(0);
    c.insert(2);
    c.insert(3);
    c.insert(4);
    c.insert(9);
    assert c.start == 3;
    assert c.end == 8;
    assert c.list[c.start..c.end] == [0,2,3,4,9];

    var f := c.has(3);
    assert c.start == 3;
    assert c.list[5] == 3;
    assert c.end == 8;

    assert f == true;

    f := c.has(213);
    assert f == false;


}