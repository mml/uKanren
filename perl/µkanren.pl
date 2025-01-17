# vim:fdm=marker:fdc=4
require 5;
use warnings;
use strict;
use diagnostics;

use feature 'signatures';

use XXX;

use constant SUBST => 0;
use constant COUNTER => 1;

### Variables {{{1
sub var($c) { bless \$c, 'Var' }
sub varp($x) { 'Var' eq ref $x }
sub var_eq($x1, $x2) {
  varp($x1) and varp($x2) and ($x1->[0] == $x2->[0]);
}

### Pairs and substitutions {{{1
use constant NIL => [];
sub cons($a, $d) { [$a, $d] }
sub pairp($x) { ref $x eq 'ARRAY' and $#$x == 1 }
sub nullp($x) { ref $x and $x == NIL }
sub car($x) { $x->[0] }
sub cdr($x) { $x->[1] }
sub ext_s($x, $v, $s) { cons(cons($x, $v), $s) }
sub empty_s() { NIL }
sub assp :prototype(&$) ($f, $l) {
  for(my $l = $l; not nullp($l); $l = cdr($l)) {
    {
      local $_ = car($l);
      return $_ if ($f->($_));
    }
  }

  return 0;
}
sub eqv($x, $y) {
  (ref $x and ref $y and $x == $y) or $x eq $y;
}

### Monad {{{1
use constant MZERO => NIL;
sub codep($x) { 'CODE' eq ref $x }
sub unit($s_c) { cons($s_c, MZERO) }
sub mplus($stream1, $stream2) {
  return $stream2 if nullp($stream1);
  return sub { mplus($stream1->(), $stream2) } if codep($stream1);
  cons(car($stream1), mplus(cdr($stream1), $stream2));
}
sub mbind($stream, $goal) {
  return MZERO if nullp($stream);
  return sub { mbind($stream->(), $goal) } if codep($stream);
  mplus($goal->(car($stream)), mbind(cdr($stream), $goal));
}

### Unification {{{1
sub walk($u, $s) {
  while (1) {
    my $pr = varp($u) && assp { var_eq($u, $_) } $s;
    return $u unless $pr;
    $u = cdr($pr);
  }
}

sub unify($u, $v, $s) {
  $u = walk($u, $s);
  $v = walk($v, $s);
  return $s if var_eq($u, $v);
  return ext_s($u, $v, $s) if varp($u);
  return ext_s($v, $u, $s) if varp($v);
  if (pairp($u) and pairp($v)) {
    my $s = unify(car($u), car($v), $s);
    return $s || unify(cdr($u), cdr($v), $s);
  }
  return eqv($u, $v) && $s;
}

### Goal Constructors {{{1
sub equ($u, $v) {
  sub ($s_c) {
    my $s = unify($u, $v, car($s_c));
    if ($s) {
      return unit(cons($s, cdr($s_c)));
    } else {
      return MZERO;
    }
  }
}

sub call_fresh($f) {
  sub($s_c) {
    my $c = cdr($s_c);
    $f->(var($c))->(cons(car($s_c), $c+1));
  }
}

sub disj($g1, $g2) {
  sub($s_c) { mplus($g1->($s_c), $g2->($s_c)) }
}
sub conj($g1, $g2) {
  sub($s_c) { mbind($g1->($s_c), $g2) }
}

### Tests {{{1
use constant EMPTY_S_C => cons(empty_s(), 0);
sub pull($stream) {
  $stream = $stream->() if codep($stream);
  return $stream;
}
sub print_answers($l, $n = 'Inf') { #{{{
  my @answers;
  for (; $n-- > 0 and not nullp($l); $l = cdr($l)) {
    $l = pull($l);
    my $s_c = car($l);
    my $s = car($s_c);
    my @lines;
    for ($s = $s; not nullp($s); $s = cdr($s)) {
      my $pr = car($s);
      my $var = car($pr);
      my $val = cdr($pr);
      push @lines, "_$$var = $val";
    }
    push @answers, join(",\n", @lines);
  }
  print join(" ;\n", @answers), ".\n\n";
} #}}}

my $result = call_fresh(sub($q) { equ($q, 5) })->(EMPTY_S_C);
print_answers($result);

my $a_and_b = conj(
  call_fresh(sub($a) { (equ($a, 7)) }),
  call_fresh(sub($b) { disj(equ($b, 5), equ($b, 6)) }));
print_answers($a_and_b->(EMPTY_S_C));

#sub fives($x) { disj(equ($x, 5), fives($x)) }
sub fives($x) { disj(
    equ($x, 5),
    sub($s_c) { # η⁻¹ delay
      sub { fives($x)->($s_c) }
    }
) }
sub sixes($x) { disj(
    equ($x, 6),
    sub($s_c) { # η⁻¹ delay
      sub { sixes($x)->($s_c) }
    }
) }
sub fives_and_sixes {
  call_fresh(
    sub($x) { disj(fives($x), sixes($x)) }
  );
}

print_answers(call_fresh(\&fives)->(EMPTY_S_C), 4);
print_answers(call_fresh(\&sixes)->(EMPTY_S_C), 4);
print_answers(fives_and_sixes->(EMPTY_S_C), 4);
