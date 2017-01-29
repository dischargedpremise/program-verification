
method mod16counter(cur: nat) returns (next: nat, ch: char)
    requires 0 <= cur < 16;
    ensures  next == (cur + 1) % 16;
    ensures ((cur == 00) ==> ch == '1') && ((cur == 01) ==> ch == '2') &&
            ((cur == 02) ==> ch == '3') && ((cur == 03) ==> ch == '4') &&
            ((cur == 04) ==> ch == '5') && ((cur == 05) ==> ch == '6') &&
            ((cur == 06) ==> ch == '7') && ((cur == 07) ==> ch == '8') &&
            ((cur == 08) ==> ch == '9') && ((cur == 09) ==> ch == 'A') &&
            ((cur == 10) ==> ch == 'B') && ((cur == 11) ==> ch == 'C') &&
            ((cur == 12) ==> ch == 'D') && ((cur == 13) ==> ch == 'E') &&
            ((cur == 14) ==> ch == 'F') && ((cur == 15) ==> ch == '0');
{
    var hexchars := ['0', '1', '2', '3', '4', '5', '6', '7',
                     '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'];

    next := (cur + 1) % 16;
    ch := hexchars[next];
}


method check_mod16counter()
{
    var next;
    var ch;

    next, ch := mod16counter(0);
    assert(next == 1 && ch == '1');

    next, ch := mod16counter(6);
    assert(next == 7 && ch == '7');

	next, ch := mod16counter(9);
	assert(next == 10 && ch == 'A');

	next, ch := mod16counter(14);
	assert(next == 15  && ch == 'F');

	next, ch := mod16counter(15);
	assert(next == 0 && ch == '0');
}
