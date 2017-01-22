
function sq(n: int) : int
{
    (n * n)
}

method check_sq()
{
    assert(sq(0) == 0);
    assert(sq(0) == sq(0));
    assert(sq(sq(0)) == sq(0));

    assert(sq(1) == sq(sq(1)));
    assert(sq(2) == 4);
    assert(sq(-2) == sq(2));

    assert(sq(sq(1)) == 1);
    assert(sq(3) + sq(4) == sq(5));
    assert(sq(-3) + sq(4) == sq(-5));
}
