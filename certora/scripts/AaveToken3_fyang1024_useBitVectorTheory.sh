if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun certora/harness/AaveTokenV3Harness.sol:AaveTokenV3 \
    --verify AaveTokenV3:certora/specs/AaveToken3_fyang1024_useBitVectorTheory.spec \
    $RULE \
    --solc solc8.13 \
    --optimistic_loop \
    --settings -useBitVectorTheory \
    --msg "AaveTokenV3:AaveToken3_fyang1024_useBitVectorTheory.spec $1"
