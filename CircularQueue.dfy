// Arthur M. Luz e Nicolle Lumertz
// 2023/01
class {:autocontracts} CircularQueue
{

    // implementation
    var lista : array<int>;
    var start : nat;
    var end   : nat;


    //abstraction
    ghost var   list: seq<int>;
    ghost var   len : nat;

    ghost predicate Valid(){
        0 <= len <= lista.Length &&
        0 <= start <= end        &&
        len == |list|            &&
        end <= lista.Length      &&
        list == if end <= lista.Length
                then lista[start..end]
                else lista[start..] + lista[..end % lista.Length]
    }
    
    constructor()
        ensures list == []
        ensures len  == 0
        {
            start := 0;
            end   := 0;
            lista := new int[6];

            list := [];
            len  := 0;
        }

    method insert(e:int)
        ensures list == old(list) + [e]
        ensures len  == len + 1
    {
        if lista.Length == (end-start){
            // cria outra fila maior
            var c := new int[lista.Length+10];
            var cEnd;
            // ja deu a volta
            if end < start{
                // copia de start -> fim dela
                forall i | start <= i < lista.Length {
                    c[i-start] := lista[i];
                }
                cEnd := lista.Length - start;
                // copia do 0 .. ate fim
                forall i | 0 <= i < (end%lista.Length) {
                    c[i+cEnd] := lista[i];
                }
                assert c[..] == lista[start..] + lista[..end % lista.Length];
            }
            // start <= end
            else{
                assert start <= end;
                forall i | start <= i < end{
                    c[i-start] := lista[i];
                }
                cEnd := end;
                //assert c[..] == lista[start..end%lista.Length];
            } 
            end := cEnd;
            start := 0;
            lista := c;
            assert list == lista[start..end];
            assert end < lista.Length;
        }
        assert list == if end <= lista.Length
                then lista[start..end]
                else lista[start..] + lista[..end % lista.Length];

        assert |list| < lista.Length;
        lista[end%lista.Length] := e;
        list := list + [e];
        len  := len + 1;
    }

    method pop() returns (e:int)
        requires |list| > 0
        ensures list    == old(list)[1..]
        ensures e       == old(list)[0]
        {
            e := lista[start];
            // se estamos no ultimo item da fila
            if start == lista.Length - 1
            {
                start := 0;
                end   := end - lista.Length;
            }
            else {
                start := start + 1;
            }
            len := len -1;
            list := list[1..];
        }

    function count(): nat
        ensures count() == (end-start)
        ensures count() == len
        {
            end-start
        }

    method has(e : int) returns (r : bool)
        requires |list| > 0
        ensures r == true  ==> e in list
        ensures r == false ==> e !in list 
        {
            if start < end % lista.Length{
                if e in lista[start..end%lista.Length]{
                    r := true;
                }
                else{
                    r := false;
                }
            }
            else {
                if e in lista[0..end]{
                    r := true;
                }
                else if e in lista[start..lista.Length]{
                    r := true;
                }
                else {
                    r := false;
                }
            }
          
        }

    function isEmpty(): bool
        ensures isEmpty() == false  ==> end - start > 0
        ensures isEmpty() == true ==> end - start == 0
        {
            end == start
        }

    static method concat(a : CircularQueue, b : CircularQueue) returns (r: CircularQueue)
        requires a.len > 0 && b.len > 0
        requires a.Valid() && b.Valid()
        ensures a.Valid() && b.Valid()
        ensures r.list[..] == a.list[..] + b.list[..]
        ensures unchanged(a)
        ensures unchanged(b)
  


}