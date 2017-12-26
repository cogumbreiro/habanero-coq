#!/bin/bash
USER="$1"
[[ -z $USER ]] && USER=cogumbreiro
git push &&
(git push --mirror git@bitbucket.org:$USER/hj-coq.git;
git push --mirror git@github.com:$USER/habanero-coq.git)
