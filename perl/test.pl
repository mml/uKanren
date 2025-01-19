use XXX;
BEGIN { unshift @INC, '.' }
use MicroKanren;

use warnings;
use strict;
use diagnostics;

use feature 'signatures';


sub len($s) {
  my $l;
  for ($l = 0; $s != NIL; $s = cdr($s)) {
    ++$l;
  }
  return $l;
}

sub reify_s($v, $s) {
  $v = walk($v, $s);
  if (varp($v)) {
    my $n = reify_name(len($s));
    return cons(cons($v, $n), $s);
  }
  return reify_s(cdr($v), reify_s(car($v), $s)) if pairp($v);
  $s;
}

sub reify_name($n) { "_$n" }

sub run_print($g, $n = 'Inf') { #{{{
  my $l = $g->(empty_state());
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
  print join(" \x1b[1;36m;\x1b[m\n", @answers), ".\n\n";
} #}}}
sub run_fresh($v, $g, $n = 'Inf') { #{{{
  my @v = split ' ', $v;
  $g = call_fresh(scalar @v, $g);
  my $l = $g->(empty_state());
  my @answers;
  if (nullp $l) {
    push @answers, "\x1b[31mfalse\x1b[m";
  }
  for (; $n-- > 0 and not nullp($l); $l = cdr($l)) {
    my $r = NIL;
    $l = pull($l);
    my $s_c = car($l);
    my $s = car($s_c);
    my @lines;
    for (my $i = 0; $i <= $#v; ++$i) {
      my $v = var($i);
      my $val = walk(walk($v, $s), $r);
      if (varp($val)) {
        $r = reify_s($val, $r);
        $val = walk($val, $r);
      }
      push @lines, "$v[$i] = $val";
    }
    push @answers, join(",\n", @lines);
  }
  print join(" \x1b[1;36m;\x1b[m\n", @answers), ".\n\n";
} #}}}
sub run_tests { ### {{{1
  run_print(call_fresh(sub($q) { equ($q, 5) }));

  my $five_or_six = call_fresh(
    goal sub($b) { equ($b, 5) | equ($b, 6) }
  );
  run_print($five_or_six);

  my $a_and_b =
    call_fresh(goal sub($a) { (equ($a, 7)) })
    & call_fresh(goal sub($b) { equ($b, 5) | equ($b, 6) });
  run_print($a_and_b);

  sub fives($x) { equ($x, 5) | Zzz { fives($x) } }
  sub sixes($x) { equ($x, 6) | Zzz { sixes($x) } }

  sub fives_and_sixes {
    call_fresh(
      sub($x) { disj(fives($x), sixes($x)) }
    );
  }

  run_print(call_fresh(\&fives), 6);
  run_print(call_fresh(\&sixes), 6);
  run_print(fives_and_sixes, 6);

  my $or = goal sub($x, $y, $r) {
      equ($x, 0) & equ($y, 0) & equ($r, 0)
    | equ($x, 0) & equ($y, 1) & equ($r, 1)
    | equ($x, 1) & equ($y, 0) & equ($r, 1)
    | equ($x, 1) & equ($y, 1) & equ($r, 1)
  };

  my $same = goal sub($a, $b, $c) {
    equ($a, $b) & equ($b, $c)
  };

  my $same_or_8 = goal sub($a, $b, $c) {
    equ($a, $b) & equ($b, $c) | equ($c, 8);
  };

  my $pair = goal sub($a, $b, $c) {
    equ($a, $b) | equ($a, $c) | equ($b, $c)
  };

  run_fresh('$x', sub($x){ equ($x, 5) });
  run_fresh('$a $c', sub($a, $c) { $same->($a, 9, $c) });
  run_fresh('$a $c', sub($a, $c) { $same_or_8->($a, 9, $c) });
  run_fresh('$a $b', sub($a, $b) { $same_or_8->($a, $b, 8) });
  run_fresh('$a $b $c', $pair);

  run_fresh('$x $y', sub($x, $y){ $or->($x, $y, 0) });
  run_fresh('$x $y', sub($x, $y){ $or->($x, $y, 1) });

  my $nullo = goal sub($x) { equ($x, NIL) };

  run_fresh('$q', sub($q){ $nullo->(NIL) });
  run_fresh('$q', sub($q){ $nullo->(cons(2, NIL)) });
  run_fresh('$q', sub($q){ $nullo->(9) });

  # TODO: Need to be able to reify other data structures (pairs).
  my $conso = goal sub($a, $d, $r) { equ(cons($a, $d), $r) };
  my $caro = goal sub($x, $a) {
    fresh(sub($d){conso($a, $d, $x)})
  };
  my $cdro = goal sub($x, $d) {
    fresh(sub($a){conso($a, $d, $x)})
  };

  run_fresh('$r', sub($r){ $conso->('foo', 'bar', $r) });
}

run_tests();

