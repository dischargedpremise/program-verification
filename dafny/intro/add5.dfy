
method add5(x: nat) returns (r: nat)
    requires 0 <= x <= 10;
    ensures  5 <= r <= (x + 5);
//    ensures  r == (x + 5);
{
    r := x + 5;
}

method use_add5()
{
    var v;

    v := add5(7);
    assert(v < 13);
    assert(v >= 5);

//    assert(v == 8);
}
