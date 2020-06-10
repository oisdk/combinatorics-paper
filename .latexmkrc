system("bash ./init-missing-lagda.sh");
system("bash ./init-lhs.sh");
system("mkdir", "-p", "out/sections");
add_cus_dep('lagda','tex',0,'lagda2tex');
add_cus_dep('lhs','tex',0,'lhs2tex');
@default_files = ('paper.tex');

sub lagda2tex {
    my $base = shift @_;
    return system("bash ./agda-from-toplevel.sh $base.lagda");
}

sub lhs2tex {
    my $base = shift @_;
    return system("bash ./haskell-from-toplevel.sh $base.lhs");
}

$aux_dir = 'out';
$out_dir = 'out';
