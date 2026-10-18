#!/usr/bin/perl
# Prints the same "<line>\t<result>" listing as run_cases, computed by Perl, for comparison.
use strict;
use warnings;
no warnings qw(experimental regexp);
use utf8;
binmode(STDOUT, ':utf8');

sub decode_subject {
    my ($s) = @_;
    $s =~ s{\\(?:(n)|(t)|(r)|(\\)|x\{([0-9A-Fa-f]+)\}|x([0-9A-Fa-f]{1,2}))}{
        defined $1 ? "\n" : defined $2 ? "\t" : defined $3 ? "\r" : defined $4 ? "\\" :
        defined $5 ? chr(hex $5) : chr(hex $6) }ge;
    return $s;
}

open(my $fh, '<:encoding(UTF-8)', $ARGV[0]) or die "$ARGV[0]: $!";
my $lineNo = 0;
while (my $l = <$fh>) {
    ++$lineNo;
    $l =~ s/[\r\n]+\z//;
    next if $l eq '' || $l =~ /^#/;
    my @c = split(/\t/, $l, -1);
    next if @c < 3;
    my ($flags, $pat, $subj) = @c;
    $pat =~ s/<LF>/\n/g;
    $subj = decode_subject($subj);
    my $mods = 'a';
    my $all = 0;
    for my $f (split //, $flags) {
        if ($f eq 'g') { $all = 1 } elsif ($f =~ /^[imsx]$/) { $mods .= $f }
    }
    my $re = eval { qr/(?$mods:$pat)/ };
    if (!defined $re) { print "$lineNo\tERR\n"; next; }
    my @results;
    my $fmt = sub {
        my @r;
        for my $g (0 .. $#+) {
            push @r, defined $-[$g] ? "$-[$g]-$+[$g]" : '-';
        }
        return join(' ', @r);
    };
    my $ok = eval {
        if ($all) {
            my $n = 0;
            while ($subj =~ /$re/g) {
                push @results, $fmt->();
                last if ++$n > 1000;
            }
        } else {
            push @results, $fmt->() if $subj =~ /$re/;
        }
        1;
    };
    if (!$ok) { print "$lineNo\tLIMIT\n"; next; }
    print "$lineNo\t", (@results ? join(';', @results) : 'NOMATCH'), "\n";
}
