method add5(x: nat) returns (r: nat)
    requires 0 <= x <= 100;
    ensures r <= (x + 5);
{
    r := x + 5;
}

method use_add5()
{
    var v;

    v := add5(7);
    assert(v <= 12);
    assert(v >= 0);
}

/**
 * NOTE: THE FOLLOWING ASSERTION FAILS!!!!
 *
 */
method check_stronger_asserts_add5()
{
    var v;

    v := add5(7);
    assert(v == 12);
}
