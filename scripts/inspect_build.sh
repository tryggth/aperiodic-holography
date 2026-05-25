#!/bin/bash
# Fetches the latest workflow run logs for inspection
echo "Fetching latest CI build run log from GitHub..."
gh run list --workflow=lean-build.yml --limit 1 --json databaseId,status,conclusion
RUN_ID=$(gh run list --workflow=lean-build.yml --limit 1 --json databaseId --jq '.[0].databaseId')
gh run view $RUN_ID --log-failed
