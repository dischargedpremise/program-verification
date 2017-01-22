/**
 * A helper function used to show how functions could be used in specifying 
 * postconditions and assertions.
 *
 */
function twice(x: int) : int
{
    (2 * x)
}

/**
 * We can use the following two postconditions. Taken together, these are 
 *  equivalent to the postcondition used in the snippet below.
 *    ensures (x == y) ==> (r == twice(x));
 *    ensures (x != y) ==> (r == x + y);
 *
 */
method sum(x: int, y: int) returns (r: int)
    ensures r == x + y;
{
    r := x + y;
}


method check_sum()
{
    var r, r2;

    r := sum(0, 0);
    assert(r == 0);

    r := sum(0, 10);
    r2 := sum(10, 0);
    assert(r == r2); // identity

    r := sum(10, 20);
    r2 := sum(20, 10);
    assert(r == r2);  // commutativity

    r := sum(10, 20);
    r := sum(r, 30);
    r2 := sum(20, 30);
    r2 := sum(10, r2);
    assert(r == r2); // associativity

    r := sum(-19, -19);
    assert(r == twice(-19));
}
