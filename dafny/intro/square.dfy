
method square(x: int) returns (res: nat)
    ensures res == x * x;
{
    res:= x*x;
}

method check_square()
{
    var r;

    r := square(0);
    assert(r == 0);

    r := square(1);
    r := square(r);
    assert(r == 1);

    var r3, r4;
    r3 := square(3);
    r4 := square(4);
    r  := square(5);
    assert(r3 + r4 == r);
}
