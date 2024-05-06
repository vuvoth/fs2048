pragma circom 2.0.3;

template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}


template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}


template Swap_IfZero() {
    signal input inps[2];
    signal output outs[2];

    component isZero = IsZero();
    isZero.in <== inps[1];

    outs[0] <== inps[0] * (1 - isZero.out);
    outs[1] <== inps[0] * isZero.out + inps[1];
}

template Join_IfEqual() {
    signal input inps[2];
    signal output outs[2];

    component equal = IsEqual();
    equal.in <== inps;

    signal tmp <== equal.out * (inps[0] + inps[1]);

    outs[1] <== (1 - equal.out) * inps[1] + tmp;
    outs[0] <== inps[0] * ( 1- equal.out);
}



template Move_Zero() {
    signal input inps[4]; 
    signal output outs[4];

    signal order[7][4]; 

    order[0] <== inps;

    var k = 0;
    var m = 0;
    component compare[6];
    for (var i = 0; i < 4; i ++) {
        for (var j = 0; j < 4 - i - 1; j++) {
            for (var h = 0; h < 4; h++) {
                if (h == j) {
                    compare[m] = Swap_IfZero();
                    compare[m].inps <== [order[k][j], order[k][j + 1]];
                    order[k + 1][h] <== compare[k].outs[0];
                    order[k + 1][h + 1] <== compare[k].outs[1];
                    m++;
                } else {
                    if (h != j + 1) {
                        order[k + 1][h] <== order[k][h];
                    }                       
                }
            }
            k++;
        }
    }
    outs <== order[6];
}




template Shift() {
    signal input inps[4];
    signal output outs[4];

    signal s[4][4];

    component m[2];

    m[0] = Move_Zero();
    m[0].inps <== inps;
    s[0] <== m[0].outs;

    var k = 3;

    signal compare[3][2];
    for (var i = 1; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            if (j != k && j != k - 1) {
                s[i][j] <== s[i - 1][j];
            } else {
                compare[i - 1] <== Join_IfEqual()([s[i - 1][k - 1], s[i - 1][k]]);
                s[i][k] <== compare[i - 1][1];
                s[i][k - 1] <== compare[i - 1][0]; 
                j++;
            }
        }
        k--;
    }

    m[1] = Move_Zero();
    m[1].inps <== s[3];
    outs <== m[1].outs;
}


template RightMove() {
    signal input inps[4][4];

    signal output outs[4][4];

    for (var i = 0; i < 4; i++) {
        outs[i] <== Shift()(inps[i]);
    }
}

template Reverse() {
    signal input inps[4]; 
    signal output outs[4];

    outs[0] <== inps[3];
    outs[1] <== inps[2];
    outs[2] <== inps[1];
    outs[3] <== inps[0];
}

template ReverseRow() {
    signal input inps[4][4];

    signal output outs[4][4];

    for (var i = 0; i < 4; i++) {
        outs[i] <== Reverse()(inps[i]);
    }
}

template Transpose() {
    signal input inps[4][4];

    signal output outs[4][4];

    for (var i =0; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            outs[i][j] <== inps[j][i];
        }
    }
}

template LeftMove() {
    signal input inps[4][4];

    signal output outs[4][4];


    signal reverse_table[4][4] <== ReverseRow()(inps);

    signal moved[4][4] <== RightMove()(reverse_table);

    outs <== ReverseRow()(moved); 
}


template UpMove() {
    signal input inps[4][4];

    signal output outs[4][4];

    signal transposed[4][4] <== Transpose()(inps);

    signal moved[4][4] <== RightMove()(transposed);

    outs <== Transpose()(moved); 
}


template DownMove() {
    signal input inps[4][4];

    signal output outs[4][4];

    signal transposed[4][4] <== Transpose()(inps);

    signal moved[4][4] <== LeftMove()(transposed);

    outs <== Transpose()(moved); 
}


template Move() {
    signal input move;
    signal input inps[4][4];
    signal output outs[4][4]; 


    signal right <== IsEqual()([move, 0]);

    signal r_table[4][4]; 
    for (var i = 0; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            r_table[i][j] <== right * inps[i][j];
        }
    }

    signal r_move_table[4][4] <== RightMove()(r_table); 

    
    signal left <== IsEqual()([move, 1]);

    signal l_table[4][4]; 
    for (var i = 0; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            l_table[i][j] <== left * inps[i][j];
        }
    }

    signal l_move_table[4][4] <== LeftMove()(l_table); 

    signal up <== IsEqual()([move, 2]);

    signal u_table[4][4]; 
    for (var i = 0; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            u_table[i][j] <== up * inps[i][j];
        }
    }

    signal up_move_table[4][4] <== UpMove()(u_table); 

    signal down <== IsEqual()([move, 2]);

    signal d_table[4][4]; 
    for (var i = 0; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            d_table[i][j] <== down * inps[i][j];
        }
    }

    signal down_move_table[4][4] <== DownMove()(d_table); 


    for (var i = 0; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            outs[i][j] <== r_move_table[i][j] + l_move_table[i][j] + up_move_table[i][j] + down_move_table[i][j];
        }
    }

    left + right + up + down === 1;
}




/*
    circom 2048
*/
template Example () {
    signal input ivc_input[4 * 4]; // IVC state = table + 1
    signal input external_inputs[1]; // 1 move

    signal output ivc_output[4 * 4]; // next IVC state = table + 1


    signal table[4][4];

    for (var i = 0; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            table[i][j] <== ivc_input[i * 4 + j];
        }
    }

    signal new_table[4][4] <== Move()(inps <== table, move <== external_inputs[0]);

    for (var i = 0; i < 4; i++) {
        for (var j = 0; j < 4; j++) {
            ivc_output[i * 4 + j] <== new_table[i][j];
        }
    }

}

component main {public [ivc_input]} = Example();
