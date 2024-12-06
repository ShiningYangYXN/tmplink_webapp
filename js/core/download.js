class download {
    parent_op = null
    download_queue = []
    download_queue_processing = false
    download_retry = 0
    download_retry_max = 10

    init(parent_op) {
        this.parent_op = parent_op;
    }

    // 启动单个文件下载
    single_start(url, filename) {
        var xhr = new XMLHttpRequest();
        xhr.addEventListener("progress", (evt) => {
            this.single_progress_on(evt, filename);
        }, false);
        xhr.addEventListener("error", (evt) => {
            if (this.download_retry < this.download_retry_max) {
                this.download_retry++;
                setTimeout(() => {
                    this.single_start(url, filename);
                }, 3000);
            } else {
                this.parent_op.alert(app.languageData.download_error_retry);
                this.single_reset();
                this.download_retry = 0;
            }
        }, false);
        xhr.addEventListener("timeout", (evt) => {
            if (this.download_retry < this.download_retry_max) {
                this.download_retry++;
                setTimeout(() => {
                    this.single_start(url, filename);
                }, 3000);
            } else {
                this.parent_op.alert(app.languageData.download_error_retry);
                this.single_reset();
                this.download_retry = 0;
            }
        }, false);
        xhr.addEventListener("abort", (evt) => {
            this.parent_op.alert(app.languageData.download_error_abort);
            this.single_reset();
        }, false);
        xhr.open("GET", url);
        xhr.onload = () => {
            this.single_complete(xhr, filename);
        };
        xhr.responseType = 'blob';
        xhr.send();
        $('.single_download_msg').html(app.languageData.download_preparing);
        $('.single_download_progress_bar').show();
        $('#btn_quick_download').attr('disabled', true);
    }

    // 单个文件下载完成处理
    single_complete(evt, filename) {
        this.download_retry = 0;
        let blob = new Blob([evt.response], {
            type: evt.response.type
        });
        if (window.navigator.msSaveOrOpenBlob) {
            navigator.msSaveBlob(blob, filename);
        } else {
            let link = document.createElement('a');
            link.href = window.URL.createObjectURL(blob);
            link.download = filename;
            link.click();
            window.URL.revokeObjectURL(link.href);
        }
        $('.single_download_msg').html(app.languageData.download_complete);
        $('.single_download_progress_bar_set').removeClass('progress-bar-animated');
        $('.single_download_progress_bar_set').removeClass('progress-bar-striped');
        this.single_reset();
        this.queue_run();
    }

    // 单个文件下载进度更新
    single_progress_on(evt) {
        $('.single_download_msg').html(app.languageData.download_progress + ' ' + bytetoconver(evt.loaded, true));
        $('.single_download_progress_bar_set').css('width', (evt.loaded / evt.total) * 100 + '%');
        $('.single_download_progress_bar_set').addClass('progress-bar-animated');
        $('.single_download_progress_bar_set').addClass('progress-bar-striped');
    }

    // 重置单个文件下载状态
    single_reset() {
        $('#btn_quick_download').removeAttr('disabled');
    }

    // 获取下载地址
    async get_download_url(ukey) {
        try {
            const recaptcha = await this.parent_op.recaptcha_do_async('download_req');
            const response = await $.post(this.parent_op.api_file, {
                action: 'download_req',
                ukey: ukey,
                token: this.parent_op.api_token,
                captcha: recaptcha
            });

            if (response.status === 1) {
                return response.data;
            } else if (response.status === 3) {
                throw new Error(app.languageData.status_need_login);
            } else {
                throw new Error(app.languageData.status_error_0);
            }
        } catch (error) {
            throw error;
        }
    }

    // 文件夹下载处理
    async folder_download(select_data) {
        try {
            // 准备文件列表并显示下载管理器
            $('#multipleDownloadModel').modal('show');
            $('#multiple_download_prepare').show();
            $('#multiple_download_processing').hide();
            
            // 初始化UI
            this.init_folder_download_progress();
            
            // 获取文件列表
            const file_list = await this.folder_download_prepare(select_data);
            
            // 计算总文件大小
            const totalSize = file_list.reduce((acc, file) => acc + parseInt(file.size), 0);
            let downloadedBytes = 0;
            
            this.append_download_info(`${app.languageData.multi_download_start} ${file_list.length} ${app.languageData.multi_download_files}, ${app.languageData.multi_download_count} ${bytetoconver(totalSize, true)}`);
            
            $('#multiple_download_prepare').hide();
            $('#multiple_download_processing').show();

            try {
                // 请求用户选择下载目录
                const dirHandle = await window.showDirectoryPicker();
                
                // 验证并获取目录权限
                const hasPermission = await this.verifyDirectoryPermissions(dirHandle);
                if (!hasPermission) {
                    throw new Error(app.languageData.folder_permission_denied || '无法获取文件夹权限');
                }

                // 显示开始下载的消息
                this.append_download_info(app.languageData.multi_download_start);
                
                // 开始处理文件
                for (let i = 0; i < file_list.length; i++) {
                    const file = file_list[i];
                    try {
                        // 获取下载链接
                        const downloadUrl = await this.get_download_url(file.ukey);
                        
                        // 创建目录结构并下载文件
                        const dirPath = file.path.split('/').slice(0, -1).join('/');
                        const fileName = file.path.split('/').pop();
                        
                        // 获取或创建目标目录
                        const targetDirHandle = dirPath ?
                            await this.ensureDirectoryExists(dirHandle, dirPath) :
                            dirHandle;
                        
                        // 下载文件并更新进度
                        await this.download_and_save_file(
                            downloadUrl, 
                            targetDirHandle, 
                            fileName, 
                            file.path,
                            (receivedBytes) => {
                                const previousFilesBytes = file_list
                                    .slice(0, i)
                                    .reduce((acc, f) => acc + parseInt(f.size), 0);
                                
                                const totalProgress = ((previousFilesBytes + receivedBytes) / totalSize) * 100;
                                
                                $('#multiple_download_process-bar')
                                    .css('width', `${totalProgress}%`)
                                    .attr('aria-valuenow', totalProgress);
                            }
                        );
                        
                        downloadedBytes += parseInt(file.size);
                        
                    } catch (error) {
                        console.error(`Error downloading file ${file.path}:`, error);
                        this.append_download_info(`${app.languageData.multi_download_error}: ${file.path} (${error.message})`);
                    }
                }
                
                // 完成所有下载
                const progressBar = $('#multiple_download_process-bar');
                progressBar.css('width', '100%')
                          .removeClass('progress-bar-animated progress-bar-striped')
                          .addClass('bg-success')
                          .attr('aria-valuenow', 100);
                
                this.append_download_info(app.languageData.multi_download_complete);
                
            } catch (error) {
                console.error('Folder download error:', error);
                this.append_download_info(`${app.languageData.multi_download_error}: ${error.message}`);
                throw error;
            }
        } catch (error) {
            this.append_download_info(`${app.languageData.multi_download_error}: ${error.message}`);
            this.parent_op.alert(app.languageData.download_error_abort);
        }
    }
    
    // 下载并保存单个文件
    async download_and_save_file(url, dirHandle, fileName, fullPath, onProgress) {
        let msgElement = null;
        
        try {
            const response = await fetch(url);
            if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`);
    
            const contentLength = parseInt(response.headers.get('content-length') || '0');
            const reader = response.body.getReader();
            const chunks = [];
            let receivedLength = 0;
    
            msgElement = this.appendProgressLine();
            this.updateProgressText(
                msgElement,
                `${app.languageData.multi_download_start}: ${fullPath} (0/${bytetoconver(contentLength, true)}) ...`
            );
    
            while (true) {
                const { done, value } = await reader.read();
                if (done) break;
                chunks.push(value);
                receivedLength += value.length;
    
                if (onProgress) {
                    onProgress(receivedLength);
                }
    
                if (contentLength && msgElement) {
                    this.updateProgressText(
                        msgElement,
                        `${app.languageData.multi_download_start}: ${fullPath} (${bytetoconver(receivedLength, true)}/${bytetoconver(contentLength, true)}) ...`
                    );
                }
            }
    
            try {
                const fileHandle = await dirHandle.getFileHandle(fileName, { create: true });
                const writable = await fileHandle.createWritable();
                await writable.write(new Blob(chunks));
                await writable.close();

                if (msgElement) {
                    this.updateProgressText(
                        msgElement,
                        `${app.languageData.multi_download_finish}: ${fullPath} (${bytetoconver(receivedLength, true)})`,
                        'text-success'
                    );
                }
            } catch (fileError) {
                throw new Error(`${app.languageData.file_write_error || '文件写入失败'}: ${fileError.message}`);
            }
    
        } catch (error) {
            if (msgElement) {
                this.updateProgressText(
                    msgElement,
                    `${app.languageData.multi_download_error}:${fullPath} (${error.message})`,
                    'text-danger'
                );
            }
            throw error;
        }
    }

    // 验证目录权限
    async verifyDirectoryPermissions(dirHandle) {
        try {
            const options = { mode: 'readwrite' };
            
            // 先检查是否已有权限
            const verifyPermission = await dirHandle.queryPermission(options);
            
            if (verifyPermission === 'granted') {
                return true;
            }
            
            // 如果没有权限，请求权限
            const permission = await dirHandle.requestPermission(options);
            return permission === 'granted';
            
        } catch (error) {
            console.error('Permission verification failed:', error);
            return false;
        }
    }

    // 创建目录结构
    async ensureDirectoryExists(rootDirHandle, dirPath) {
        const parts = dirPath.split('/');

        let currentHandle = rootDirHandle;

        for (const part of parts) {
            if (part) {
                try {
                    currentHandle = await currentHandle.getDirectoryHandle(part, { create: true });
                } catch (error) {
                    console.error(`Error creating directory ${part}:`, error);
                    throw new Error(`${app.languageData.folder_create_error || '创建文件夹失败'}: ${error.message}`);
                }
            }
        }

        return currentHandle;
    }

    // 处理选中的文件信息
    async folder_download_prepare(select_data) {
        let file_list = [];
        for (let x in select_data) {
            if (select_data[x].type === 'dir') {
                try {
                    let response = await $.post(this.parent_op.api_mr, {
                        action: 'get_all_file',
                        token: this.parent_op.api_token,
                        mr_id: select_data[x].id
                    });

                    if (response.status === 1) {
                        file_list.push(...response.data);
                    } else {
                        console.error('API returned error status:', response);
                    }
                } catch (error) {
                    console.error('jQuery post error:', error);
                }
            } else {
                this.parent_op.dir.file_list.forEach((item) => {
                    if (item.ukey === select_data[x].id) {
                        file_list.push({
                            ukey: item.ukey,
                            size: item.filesize,
                            path: item.fname
                        });
                    }
                });
            }
        }
        return file_list;
    }

    // 添加进度行并返回元素引用
    appendProgressLine() {
        const infoArea = $('#multiple_download_info');
        const msgDiv = $('<div class="download-message mb-1"></div>');
        infoArea.prepend(msgDiv);
        infoArea.scrollTop(0);
        return msgDiv;
    }

    // 更新进度文本
    updateProgressText(element, message, className = '') {
        if (!element) return;
        const timestamp = new Date().toLocaleTimeString();
        element.attr('class', 'download-message mb-1 ' + className)
               .html(`[${timestamp}] ${message}`);
    }

    // 初始化下载进度UI
    init_folder_download_progress() {
        const progressBar = $('#multiple_download_process-bar');
        progressBar.css('width', '0%')
            .removeClass('bg-success')
            .addClass('progress-bar-striped progress-bar-animated')
            .attr('aria-valuenow', 0);

        $('#multiple_download_info').empty();
    }

    // 添加普通信息
    append_download_info(message) {
        const timestamp = new Date().toLocaleTimeString();
        const msgElement = this.appendProgressLine();
        this.updateProgressText(msgElement, message);
    }
}