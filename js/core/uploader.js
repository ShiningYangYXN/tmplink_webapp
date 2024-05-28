class uploader {
    parent_op = null

    skip_upload = false
    prepare_sha1 = false
    mr_id = 0
    upload_count = 0
    upload_queue_id = 0
    upload_queue_file = []
    upload_processing = 0
    single_file_size = 50 * 1024 * 1024 * 1024
    slice_size = 3 * 1024 * 1024;
    max_sha1_size = 256 * 1024 * 1024;

    upload_queue = 0;
    upload_queue_max = 5;

    // 单个文件的上传线程数
    upload_worker_queue = [];
    upload_worker_queue_max = 5;

    upload_slice_chunk = [] //记录每个文件的总上传量
    upload_slice_total = [] //文件上传线程计数器
    upload_slice_process = [] //当前处理进度

    worker_speed = 0
    upload_speed = 0

    init(parent_op) {
        this.parent_op = parent_op;
        this.quickUploadInit();
        this.speed_updater();
    }

    init_upload_pf(){
        $.post(this.parent_op.api_user, {
            'action': 'pf_upload_get',
            'token': this.parent_op.api_token
        }, (rsp) => {
            if (rsp.status === 1) {
                this.upload_worker_queue_max = rsp.data.upload_slice_thread_max;
                this.upload_queue_max = rsp.data.upload_slice_queue_max;
                this.slice_size = rsp.data.upload_slice_size * (1024*1024);
                //更新到界面
                $('#upload_slice_size').val(rsp.data.upload_slice_size);
                $('#upload_slice_queue_max').val(rsp.data.upload_slice_queue_max);
                $('#upload_slice_thread_max').val(rsp.data.upload_slice_thread_max);
            }
        }, 'json');
        //如果用户还不是赞助者，将不支持修改上传参数
        if(this.parent_op.isSponsor===false){
            $('#upload_slice_size').attr('disabled','disabled');
            $('#upload_slice_queue_max').attr('disabled','disabled');
            $('#upload_slice_thread_max').attr('disabled','disabled');
        }
    }

    auto_set_upload_pf(dom){
        //获取当前值
        let val = $(dom).val();
        //输入的值不能大于 100，不能小于 1
        if(val>100){
            val = 100;
        }
        if(val<1){
            val = 1;
        }
        //获取当前的 ID
        let id = $(dom).attr('id');
        //更新前，更改输入框的颜色
        $(dom).addClass('text-yellow');
        //更新
        $.post(this.parent_op.api_user, {
            'action': 'pf_upload_set',
            'token': this.parent_op.api_token,
            'key': id,
            'val': val
        }, (rsp) => {
            //恢复输入框的颜色
            $(dom).removeClass('text-yellow');
            if (rsp.status === 1) {
                //将输入框设置为绿色
                $(dom).addClass('text-success');
                setTimeout(() => {
                    $(dom).removeClass('text-success');
                }, 1000);
                //更新本地配置的对应值
                switch(id){
                    case 'upload_slice_size':
                        this.slice_size = val * (1024*1024);
                        break;
                    case 'upload_slice_queue_max':
                        this.upload_queue_max = val;
                        break;
                    case 'upload_slice_thread_max':
                        this.upload_worker_queue_max = val;
                        break;
                }
            } else {
                //将输入框设置为红色
                $(dom).addClass('text-danger');
                setTimeout(() => {
                    $(dom).removeClass('text-danger');
                }, 1000);
            }
        }, 'json');
    }

    tmpupGenerator() {
        $('#tmpup').show();
        this.parent_op.btn_copy_bind();
    }

    tmpupGeneratorView() {
        //如果有设定文件夹
        let mrid = get_page_mrid();
        let model = localStorage.getItem('app_upload_model');
        let token = this.parent_op.api_token;

        //显示 Token
        $('#tmpup_mrid_view').hide();
        $('#tmpup_token').html(token);
        $('#tmpup_copy_token').attr('onclick', `TL.directCopy(this,'${token}')`);
        $('#tmpup_model').html(model);
        $('#tmpup_copy_model').attr('onclick', `TL.directCopy(this,'${model}')`);

        if (mrid !== undefined) {
            $('#tmpup_mrid_view').show();
            $('#tmpup_mrid').html(mrid);
            $('#tmpup_copy_mrid').attr('onclick', `TL.directCopy(this,'${mrid}')`);
        } else {
            $('#tmpup_mrid_view').hide();
        }
    }

    skipUpload() {
        this.skip_upload = ($('#skip_upload').is(':checked')) ? true : false;
        //启用此功能，需要同时启用秒传 quickUpload
        if (this.prepare_sha1 === false && this.skip_upload === true) {
            console.log('Enable quick upload');
            this.prepare_sha1 = true;
            $('#quick_upload').prop('checked', true);
        }

    }

    quickUploadInit() {
        if (localStorage.getItem('app_upload_quick') === null) {
            localStorage.setItem('app_upload_quick', 0);
        } else {
            if (localStorage.getItem('app_upload_quick') === '1') {
                $('#quick_upload').prop('checked', true);
                this.prepare_sha1 = true;
            } else {
                $('#quick_upload').prop('checked', false);
                this.prepare_sha1 = false;
            }
        }
    }

    quickUpload() {
        //写入到存储
        localStorage.setItem('app_upload_quick', ($('#quick_upload').is(':checked')) ? 1 : 0);
        this.prepare_sha1 = ($('#quick_upload').is(':checked')) ? true : false;
        //如果此功能被设置为 false，那么需要同时关闭跳过上传
        if (this.skip_upload === true && this.prepare_sha1 === false) {
            console.log('Disable skip upload');
            this.skip_upload = false;
            $('#skip_upload').prop('checked', false);
        }
    }

    upload_queue_clean() {
        $('.upload_file_ok').remove();
        if (this.upload_queue_file.length > 0) {
            for (let x in this.upload_queue_file) {
                $('#uq_' + id).remove();
            }
            this.upload_queue_file = [];
        }
    }

    upload_cli() {
        if (this.parent_op.logined === 1) {
            $('#uploadCliModal').modal('show');
            $('#upload_cli_token').html(this.parent_op.api_token);
        } else {
            this.parent_op.alert(app.languageData.status_need_login);
            app.open('/app&listview=login');
        }
    }

    open(mr_id) {

        this.mr_id = mr_id;

        if (!this.parent_op.logined) {
            this.parent_op.alert(app.languageData.status_need_login);
            return false;
        }

        if (mr_id == 0) {
            $('#dirsToUpload').hide();
            $('.dirsToUpload_label').hide();
        }

        // this.upload_model_selected(Number(this.upload_model_selected_val));

        $('#upload_mr_id').val(mr_id);

        //如果可用的私有空间不足，则隐藏选项
        if (this.storage_used >= this.storage) {
            $('.storage_needs').hide();
        }

        //skip upload
        if (this.skip_upload) {
            $('#skip_upload').attr('checked', 'checked');
        }

        $('#uploadModal').modal('show');

        this.tmpupGeneratorView();
    }

    /**
     * 开始上传，如果没有超过最大上传数，启动新的上传任务
     */
    upload_start() {

        //如果没有需要上传的文件，退出
        if (this.upload_queue_file.length == 0) {
            return false;
        }

        //如果超过最大上传数，等待 1 秒后再次检查
        if (this.upload_queue > this.upload_queue_max) {
            //等待 1 秒后再次检查
            setTimeout(() => {
                this.upload_start();
            }, 1000);
            return false;
        }

        //启动新的上传任务
        let f = this.upload_queue_file.shift();
        this.upload_queue++;
        if (typeof f === 'object') {
            this.upload_core(f, f.is_dir);
        }
    }

    queue_remove(id) {
        // delete this.upload_queue_file[id];
        // this.upload_queue_file.length--;

        for (var i = 0; i < this.upload_queue_file.length - 1; i++) {
            if (this.upload_queue_file[i].id == id) {
                this.upload_queue_file.splice(i, 1);
            }
        }

        $('#uq_' + id).hide();
    }

    upload_model_get() {
        return $("#upload_model").val();
    }

    upload_mrid_get() {
        return $("#upload_mr_id").val();
    }

    upload_core(file_res, is_dir) {
        $('#nav_upload_btn').html('<img src="/img/loading.svg"  />');
        let file = file_res.file;
        let id = file_res.id;
        let model = file_res.model;
        let mrid = file_res.mrid;
        if (file.size > this.single_file_size) {
            this.parent_op.alert(app.languageData.upload_limit_size);
            $('#uq_' + id).fadeOut();
            this.upload_queue--;
            return false;
        }

        if (file.size > (this.storage - this.storage_used) && (model == 99)) {
            this.parent_op.alert(app.languageData.upload_fail_storage);
            $('#uq_' + id).fadeOut();
            this.upload_queue--;
            return false;
        }
        $('#uq_delete_' + id).hide();
        $('#uqnn_' + id).html(app.languageData.upload_upload_prepare);

        this.upload_prepare(file, id, (f, sha1, id) => {
            //如果sha1不等于0，则调用另外的接口直接发送文件名信息。
            let filename = is_dir ? file.webkitRelativePath : file.name;
            let upload_skip = this.skip_upload ? 1 : 0;
            if (sha1 !== 0) {
                //如果启用了跳过文件
                if (this.skip_upload) {
                    $.post(this.parent_op.api_file, {
                        'sha1': sha1,
                        'mr_id': mrid,
                        'action': 'check_in_dir',
                        'token': this.parent_op.api_token
                    }, (rsp) => {
                        switch (rsp.status) {
                            //文件尚未上传到服务器
                            case 0:
                                this.upload_worker(f, sha1, id, filename);
                                break;
                            //文件已被上传，并且已经在文件夹中
                            case '1':
                                this.upload_final(rsp, file, id, true);
                                break;
                            //文件已被上传,但是不在文件中，调用 prepare 处理
                            case '2':
                                $.post(this.parent_op.api_file, {
                                    'sha1': sha1,
                                    'filename': filename,
                                    'filesize': file.size,
                                    'model': model,
                                    'mr_id': mrid,
                                    'skip_upload': upload_skip,
                                    'action': 'prepare_v4',
                                    'token': this.parent_op.api_token
                                }, (rsp) => {
                                    if (rsp.status === 1) {
                                        this.upload_final(rsp, file, id);
                                    } else {
                                        this.upload_worker(f, sha1, id, filename);
                                    }
                                }, 'json');
                                break;
                        }
                    }, 'json');
                } else {
                    $.post(this.parent_op.api_file, {
                        'sha1': sha1,
                        'filename': filename,
                        'filesize': file.size,
                        'model': model,
                        'mr_id': mrid,
                        'skip_upload': upload_skip,
                        'action': 'prepare_v4',
                        'token': this.parent_op.api_token
                    }, (rsp) => {
                        if (rsp.status === 1) {
                            this.upload_final(rsp, file, id);
                        } else {
                            this.upload_worker(f, sha1, id, filename);
                        }
                    }, 'json');
                }
            } else {
                this.upload_worker(f, sha1, id, filename);
            }
        });
    }

    model_selected(model) {
        //检查账号是否有足够可用的空间
        if (model == 99) {
            if (this.storage_used >= this.storage) {
                alert('私有空间已经用完，请考虑购买私有空间扩展包。');
                return false;
            }
        }

        switch (model) {
            case 0:
                $('#seleted_model').html(app.languageData.modal_settings_upload_model1);
                $('#upload_model').val(0);
                break;
            case 1:
                $('#seleted_model').html(app.languageData.modal_settings_upload_model2);
                $('#upload_model').val(1);
                break;
            case 2:
                $('#seleted_model').html(app.languageData.modal_settings_upload_model3);
                $('#upload_model').val(2);
                break;
            case 3:
                $('#seleted_model').html(app.languageData.modal_settings_upload_model4);
                $('#upload_model').val(3);
                break;
            case 99:
                $('#seleted_model').html(app.languageData.modal_settings_upload_model99);
                $('#upload_model').val(99);
                break;
        }
        $('#select_model_list').hide();
        $('#upload_select_file').show();
        $('#selected_model_box').show();
        localStorage.setItem('app_upload_model', model);
    }

    model_reset() {
        $('#select_model_list').show();
        $('#upload_select_file').hide();
        $('#selected_model_box').hide();
    }


    upload_prepare(file, id, callback) {
        // 定义块大小为 64KB
        const blockSize = 64 * 1024;
        // 定义 SHA-1 实例
        const sha1 = CryptoJS.algo.SHA1.create();
        // 定义当前块号和总块数
        let currentBlock = 0;
        const totalBlocks = Math.ceil(file.size / blockSize);
        // 定义进度条元素
        let uqpid = "#uqp_" + id;
        const progressBar = $(uqpid);

        // 提取信息
        $('#uqnn_' + id).html(app.languageData.upload_upload_prepare);

        // 不支持 FileReader , 或者停用了秒传，或者文件大小超过了 max_sha1_size 直接下一步。
        if (!window.FileReader || this.prepare_sha1 === false) {
            callback(file, 0, id);
            return false;
        }

        // 支持 FileReader，计算 SHA-1 值
        const reader = new FileReader();
        reader.onload = function () {
            // 读取当前块数据
            const data = new Uint8Array(reader.result);
            // 更新 SHA-1 实例
            sha1.update(CryptoJS.lib.WordArray.create(data));
            // 更新当前块号
            currentBlock++;

            // 更新进度条
            const progress = currentBlock / totalBlocks * 100;
            progressBar.css('width', `${progress}%`);

            // 如果当前块号小于总块数，则继续读取下一块
            if (currentBlock < totalBlocks) {
                readNextBlock();
            } else {
                // 如果所有块都读取完毕，则计算最终 SHA-1 值并回调
                const hash = sha1.finalize().toString();
                callback(file, hash, id);
            }
        };

        // 读取下一块数据
        function readNextBlock() {
            const start = currentBlock * blockSize;
            const end = Math.min(start + blockSize, file.size);
            reader.readAsArrayBuffer(file.slice(start, end));
        }

        // 初始化进度条
        progressBar.css('width', '0%');

        // 从第一块开始读取数据
        readNextBlock();
    }



    upload_worker(file, sha1, id, filename) {
        //sha1 在浏览器不支持 sha1 计算，或者停用了秒传，其值为 0

        //获取上传服务器的节点
        this.parent_op.recaptcha_do('upload_request_select2', (captcha) => {
            $.post(this.parent_op.api_url_upload, {
                'token': this.parent_op.api_token,
                'action': 'upload_request_select2',
                'filesize': file.size,
                'captcha': captcha,
            }, (rsp) => {
                if (rsp.status == 1) {
                    //文件小于 32 MB，直接上传
                    console.log('upload::slice::' + filename);
                    let api_sync = rsp.data.uploader + '/app/upload_slice';
                    this.worker_slice(api_sync, rsp.data.utoken, sha1, file, id, filename, 0);
                } else {
                    //无法获得可用的上传服务器
                    this.parent_op.alert('上传失败，无法获得可用的服务器。');
                }
            });
        });
    }

    /**
     * 分片上传
     * 分片上传功能，首先会查询服务器是否有需要上传的分片，如果有则返回分片编号，如果没有则返回需要上传的分片编号
     * @param {*} server
     * @param {*} file 
     * @param {*} id 
     * @param {*} filename 
     */
    worker_slice(server, utoken, sha1, file, id, filename, thread = 0) {

        //如果没有初始化，则初始化，并将当前任务设置为主线程，只有主线程才能更新界面
        if(thread === 0){
            if (this.upload_slice_chunk[id] === undefined) {
                this.upload_slice_chunk[id] = [];
            }
            if(this.upload_slice_process[id] === undefined){
                this.upload_slice_process[id] = 0;
            }
        }

        //创建分片任务的ID，算法 uid+文件路径+文件大小 的 sha1 值
        let uptoken = CryptoJS.SHA1(this.parent_op.uid + file.name + file.size).toString();
        let upload_queue_max = this.upload_worker_queue_max;
        let numbers_of_slice = 1;

        //根据当前分片限制，以及文件的总大小，计算出是否启动多线程上传
        if (file.size > this.slice_size) {
            numbers_of_slice = Math.ceil(file.size / this.slice_size);
        }

        //如果分片数量大于上传线程数量，则线程数量设定为 upload_queue_max,否则设定为 numbers_of_slice
        if (numbers_of_slice < upload_queue_max) {
            upload_queue_max = numbers_of_slice;
        }

        //尚未初始化线程分配总数
        if (this.upload_slice_total[id] === undefined) {
            this.upload_slice_total[id] = numbers_of_slice;
        }

        //当前任务的多线程上传队列状态是否已经建立
        if (this.upload_worker_queue[id] === undefined) {
            this.upload_worker_queue[id] = 1;
            // console.log(`任务 ${id} 主线程 1 已启动。`);
        }

        //如果当前处理进度 -1 等于总数，并且不是主线程，则退出
        if ((this.upload_slice_process[id] - 3) >= numbers_of_slice && thread > 0) {
            // console.log(`任务 ${id} 子线程已退出。`);
            return false;
        } else {
            //更新进度
            this.upload_slice_process[id]++;
            //是否超出上传线程数？没有超出的话，启动新的上传任务
            if (this.upload_worker_queue[id] < upload_queue_max) {
                let thread_id = this.upload_worker_queue[id]+1;
                this.upload_worker_queue[id] = thread_id;
                this.worker_slice(server, utoken, sha1, file, id, filename, thread_id);
                // console.log(`任务 ${id} 子线程 ${thread_id} 已启动。`);
            }
        }

        //查询分片信息
        $.post(server, {
            'token': this.parent_op.api_token, 'uptoken': uptoken,
            'action': 'prepare',
            'sha1': sha1, 'filename': filename, 'filesize': file.size, 'slice_size': this.slice_size,
            'utoken': utoken, 'mr_id': this.upload_mrid_get(), 'model': this.upload_model_get()
        }, (rsp) => {

            switch (rsp.status) {
                /**
                 * 分片上传服务
                 * 返回状态码
                 * 1 ：上传完成
                 * 2 ：上传尚未完成，需要等待其他人完成上传（客户端每隔一段时间再次发起查询，如果用户无法完成上传，则重新分配）
                 * 3 ：进入上传流程，客户端将会获得一份分配的分片编号
                 * 4 ：分片任务不存在
                 * 5 ：分片上传完成
                 * 6 ：这个文件已经被其他人上传了，因此直接跳过（需要清理已上传的文件）
                 * 7 : 上传失败，原因将会写入到 data
                 * 8 ：分片合并完成
                 * 9 ：文件已经上传完成，但是文件合并进程正在进行中，处于锁定状态
                 */
                case 1:
                    //已完成上传
                    this.upload_final({ status: rsp.status, data: { ukey: rsp.data } }, file, id);
                    break;
                case 6:
                    //已完成上传
                    //重置 rsp.stustus = 1
                    rsp.status = 1;
                    this.upload_final({ status: rsp.status, data: { ukey: rsp.data } }, file, id);
                    break;
                case 8:
                    //已完成上传
                    //重置 rsp.stustus = 1
                    //重置 rsp.ukey = rsp.data ，模板中需要用到
                    rsp.status = 1;
                    this.upload_final({ status: rsp.status, data: { ukey: rsp.data } }, file, id);
                    break;
                case 2:
                    //没有可上传分片，等待所有分片完成
                    //只有主线程才执行这项工作，其他线程直接退出
                    setTimeout(() => {
                        this.worker_slice(server, utoken, sha1, file, id, filename, thread);
                    }, 5000);
                    break;
                case 3:
                    //获得一个需要上传的分片编号,开始处理上传
                    this.worker_slice_uploader(server, id, uptoken, file, rsp.data, filename, thread, () => {
                        //回归
                        this.worker_slice(server, utoken, sha1, file, id, filename, thread);
                    });

                    break;
                case 7:
                    //上传失败
                    //rsp.data 中的数值为错误代码
                    this.upload_final({ status: rsp.data, data: { ukey: rsp.data } }, file, id, thread);
                    break;
                case 9:
                    //重置 rsp.stustus = 1
                    rsp.status = 1;
                    this.upload_final({ status: rsp.status, data: { ukey: rsp.data } }, file, id,);
                    break;

            }
        }, 'json');
    }

    /**
     * 分片上传
     */
    worker_slice_uploader(server, id, uptoken, file, slice_status, filename, thread, cb) {
        //从 file 中读取指定的分片
        let index = slice_status.next;
        let blob = file.slice(index * this.slice_size, (index + 1) * this.slice_size);

        //初始化
        let uqmid = "#uqm_" + id;
        let uqpid = "#uqp_" + id;
        let main_t = thread === 0 ? '主线程' : '子线程';

        //如果是最后一个分片，只有主线程才执行这项工作，其他线程直接退出
        // if(index>=(this.upload_slice_total[id]-2)&&thread===false){
        //     console.log(`任务 ${id} ${main_t} 已退出。`);
        //     return false;
        // }

        // console.log(`任务 ${id} ${main_t} ${thread} 正在上传分片 ${index}。`);

        //初始化上传任务的已上传数据计数器
        if (this.upload_slice_chunk[id][index] === undefined) {
            this.upload_slice_chunk[id][index] = 0;
        }

        //提交分片
        let xhr = new XMLHttpRequest();
        //构建参数
        let fd = new FormData();
        fd.append("filedata", blob, 'slice');
        fd.append("uptoken", uptoken);
        fd.append("filename", filename);
        fd.append("index", index);
        fd.append("action", 'upload_slice');
        fd.append("slice_size", this.slice_size);

        //完成时回调
        xhr.addEventListener("load", (evt) => {
            //将返回值解析为 json
            let rsp = JSON.parse(evt.target.response);
            //如果返回值是 5，则表示分片上传完成
            if (rsp.status == 5) {
                cb();
            } else {
                //其它情况也返回处理
                cb();
            }
        });

        //主线程工作
        if (thread === 0) {
            //如果是主线程，则更新上传信息到界面上
            $('#uqnn_' + id).html(app.languageData.upload_sync);

            //获取进度信息
            let total = slice_status.total;
            let success = slice_status.total - slice_status.wait;

            //设置进度条的宽度
            let pp_pie = 100 / total;
            let pp_percent = success * pp_pie;

            //绘制进度信息
            $(uqmid).html(`${app.languageData.upload_upload_processing} ${file.name}`);
            $(uqpid).css('width', pp_percent + '%');
        }

        //上传完成后，关闭计时器
        xhr.addEventListener("loadend", (evt) => {
            //如果已上传的总数等于总数，则表示上传完成，显示已完成
            if (index === (this.upload_slice_total[id] - 1)) {
                $('#uqnn_' + id).html(app.languageData.upload_sync_onprogress);
                $(uqpid).css('width', '100%');
            }
        });

        //上传发生错误，重启
        xhr.addEventListener("error", (evt) => {
            cb();
        });

        //分块上传进度上报
        xhr.upload.onprogress = (evt) => {
            if (evt.lengthComputable) {
                //计算出本次上传量
                let loaded = evt.loaded - this.upload_slice_chunk[id][index];
                //记录到已上传总量中
                this.upload_speed += parseInt(loaded);
                //更新数据
                this.upload_slice_chunk[id][index] = evt.loaded;
            }
        };

        //提交
        xhr.overrideMimeType("application/octet-stream");
        xhr.open("POST", server);

        this.parent_op.recaptcha_do('upload_slice', (recaptcha) => {
            fd.append('captcha', recaptcha);
            xhr.send(fd);
        });
    }

    speed_updater() {
        if (this.worker_speed === 0) {
            //尚未初始化，开始初始化
            this.worker_speed = setInterval(() => {
                if (this.upload_speed > 0) {
                    //计算速度
                    let speed_text = bytetoconver(this.upload_speed, true) + '/s';
                    //更新到界面
                    $('.upload_speed_show_inner').show();
                    $('.upload_speed_show_inner').html(speed_text);
                    //重置为 0
                    this.upload_speed = 0;
                } else {
                    $('.upload_speed_show_inner').hide();
                }
            }, 1000);
        }
    }

    selected(dom) {
        //隐藏首页特性的介绍
        $('#index_feature').fadeOut();

        let file = document.getElementById('fileToUpload').files;
        let f = null;
        if (file.length > 0) {
            for (let x in file) {
                f = file[x];
                if (typeof f !== 'object') {
                    continue;
                }
                if (f.size !== 0) {
                    this.upload_queue_add({
                        file: f,
                        is_dir: false
                    });
                }
            }
        }

        //清空文件选择框
        dom.value = '';
    }

    dir_selected(e) {
        let file = document.getElementById('dirsToUpload').files;
        let f = null;
        if (file.length > 0) {
            for (let x in file) {
                f = file[x];
                if (typeof f !== 'object') {
                    continue;
                }
                if (f.size !== 0) {
                    this.upload_queue_add({
                        file: f,
                        is_dir: true
                    });
                }
            }
        }
        //清空文件选择框
        // dom.value = '';
    }


    drop(e) {
        e.preventDefault();
        var fileList = e.dataTransfer.files;
        //files
        if (fileList.length == 0) {
            return false;
        }
        for (let x in fileList) {
            if (typeof fileList[x] === 'object') {
                setTimeout(() => {
                    this.upload_queue_add({
                        file: fileList[x],
                        is_dir: false
                    });
                }, 500);
            }
        }

    }

    upload_queue_add(f) {
        setTimeout(() => {
            let file = f.file;

            //添加一些额外参数
            f.model = this.upload_model_get();
            f.mrid = this.upload_mrid_get();
            f.id = this.upload_queue_id;

            //检查是否超出了可用的私有存储空间
            if (this.upload_model_get() == 99) {
                if ((this.parent_op.storage_used + file.size) > this.parent_op.storage) {
                    $.notifi(file.name + ' : ' + app.languageData.upload_fail_storage, { noticeClass: 'ntf-error', autoHideDelay: 5000 });
                    return false;
                }
            }

            this.upload_queue_file.push(f);
            //如果未登录，添加队列到首页
            let target = this.parent_op.isLogin() ? '#upload_model_box' : '#upload_index_box';
            $(target).append(app.tpl('upload_list_wait_tpl', {
                name: file.name,
                size: bytetoconver(file.size, true),
                id: this.upload_queue_id
            }));
            $(target).show();
            this.upload_queue_id++;
            //更新状态
            this.upload_btn_status_update();
            //启动上传
            this.upload_start();
        }, 500, f);
    }

    upload_btn_status_update() {
        if (this.upload_queue_file.length > 0) {
            //更新队列数
            $('.upload_queue').fadeIn();
            $('.upload_queue_counter').html(this.upload_queue_file.length);

            //更新已完成📖
            $('.upload_count').fadeIn();
            $('.upload_count').html(this.upload_count);
        } else {
            $('.upload_queue').fadeOut();
        }
    }

    upload_complete(evt, file, id) {
        this.download_retry = 0;
        clearInterval(this.upload_progressbar_counter[id]);
        this.upload_progressbar_counter[id] = null;
        var data = JSON.parse(evt.target.responseText);
        this.upload_final(data, file, id);
    }

    upload_failed(evt, id) {
        clearInterval(this.upload_progressbar_counter[id]);
        this.upload_progressbar_counter[id] = null;
        this.parent_op.alert(app.languageData.upload_fail);
        this.upload_queue--;
        $('#uq_' + id).fadeOut();
    }

    upload_canceled(evt, id) {
        clearInterval(this.upload_progressbar_counter[id]);
        this.upload_progressbar_counter[id] = null;
        this.parent_op.alert(app.languageData.upload_cancel);
        this.upload_queue--;
        $('#uq_' + id).fadeOut();
    }

    upload_final(rsp, file, id, skip) {
        this.upload_queue--;
        if (skip === undefined) {
            skip = false;
        }
        //$('#nav_upload_btn').html(app.languageData.nav_upload);
        if (rsp.status === 1) {
            $('#uqnn_' + id).html(app.languageData.upload_ok);

            //如果未登录状态下上传，则不隐藏上传完成后的信息
            if (this.parent_op.isLogin()) {
                if (get_page_mrid() != undefined && this.upload_queue_file.length == 0) {
                    this.parent_op.room_list();
                }
                if (get_page_mrid() == undefined && this.upload_queue_file.length == 0) {
                    this.parent_op.workspace_filelist(0);
                }
                $('#uq_' + id).hide();
                if (skip === false) {
                    $('#upload_model_box_finish').append(app.tpl('upload_list_ok_tpl', {
                        name: file.name,
                        size: bytetoconver(file.size, true),
                        ukey: rsp.data.ukey
                    }));
                    this.parent_op.btn_copy_bind();
                }
                this.upload_btn_status_update();
            } else {
                $('#uq_' + id).remove();
                $('#upload_index_box_finish').show();
                $('#upload_index_box_finish').append(app.tpl('upload_list_ok_tpl', {
                    name: file.name,
                    size: bytetoconver(file.size, true),
                    ukey: rsp.data.ukey
                }));
                this.parent_op.btn_copy_bind();
            }
        } else {
            //根据错误代码显示错误信息
            let error_msg = app.languageData.upload_fail;
            switch (rsp.status) {
                case 2:
                    //上传失败，无效请求
                    error_msg = app.languageData.upload_fail_utoken;
                    break;
                case 3:
                    //上传失败，不能上传空文件
                    error_msg = app.languageData.upload_fail_empty;
                    break;
                case 4:
                    //上传失败，上传的文件大小超出了系统允许的大小
                    error_msg = app.languageData.upload_limit_size;
                    break;
                case 5:
                    //上传失败，超出了单日允许的最大上传量
                    error_msg = app.languageData.upload_limit_day;
                    break;
                case 6:
                    //上传失败，没有权限上传到这个文件夹
                    error_msg = app.languageData.upload_fail_permission;
                    break;
                case 7:
                    //要上传的文件超出了私有存储空间限制
                    error_msg = app.languageData.upload_fail_storage;
                    break;
                case 8:
                    //上传失败，目前暂时无法为这个文件分配存储空间
                    error_msg = app.languageData.upload_fail_prepare;
                    break;
                case 9:
                    //上传失败，操作失败，无法获取节点信息
                    error_msg = app.languageData.upload_fail_node;
                    break;
                case 10:
                    //上传失败，文件名中包含了不允许的字符
                    error_msg = app.languageData.upload_fail_name;
                    break;
                default:
                    //默认错误
                    error_msg = app.languageData.upload_fail_unknown + ` ${rsp.status}`;
            }
            console.log(rsp.status + ':' + error_msg);
            $('#uqnn_' + id).html(`<span class="text-red">${error_msg}</span>`);
            //清除上传进度条
            $('.uqinfo_' + id).remove();
        }

        //更新上传统计
        this.upload_count++;
    }

    upload_final_error_text(status) {
        switch (status) {
            case 2:
                //上传失败，无效请求
                return app.languageData.upload_fail_utoken;
            case 3:
                //上传失败，不能上传空文件
                return app.languageData.upload_fail_empty;
            case 4:
                //上传失败，上传的文件大小超出了系统允许的大小
                return app.languageData.upload_limit_size;
            case 5:
                //上传失败，超出了单日允许的最大上传量
                return app.languageData.upload_limit_day;
            case 6:
                //上传失败，没有权限上传到这个文件夹
                return app.languageData.upload_fail_permission;
            case 7:
                //要上传的文件超出了私有存储空间限制
                return app.languageData.upload_fail_storage;
            case 8:
                //上传失败，目前暂时无法为这个文件分配存储空间
                return app.languageData.upload_fail_prepare;
            case 9:
                //上传失败，操作失败，无法获取节点信息
                return app.languageData.upload_fail_node;
            case 10:
                //上传失败，文件名中包含了不允许的字符
                return app.languageData.upload_fail_name;
            default:
                //默认错误
                return app.languageData.upload_fail_unknown + ` ${status}`;
        }
    }
}