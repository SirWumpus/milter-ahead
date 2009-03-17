#!/usr/bin/awk
#
# Convert a mailertable source file into a source file suitable
# for call-ahead-db.
# 
# usage: awk -f convert-mailertable.awk mailertable >call-ahead-db.txt
#

$2 ~ /^local:/ {
	next
}

$2 ~ /^[^:]*smtp:/ {
	sub("^[^:]*smtp:", "", $2)
	print $1, $2
}